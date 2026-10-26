import V185TrunkScan22Chunk301

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2693457 : List Nat := [1, 2, 2, 1, 4, 4, 8]
def baseStart_2693457 : Nat := 118140960795 + 2693457 * 2 ^ 59
def prefixEnd_2693457 : Nat := 4983230072969 + 3 ^ 40 * 2693457 * 2
def baseEnd_2693457 : Nat := 34149087980670952365445

theorem tailTrace_2693457 : CollatzResearch.WordTrace tailWord_2693457 prefixEnd_2693457 34149087980670952365445 := by
  unfold tailWord_2693457
  simp only [CollatzResearch.WordTrace]
  refine ⟨98238447403072769677774625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65492298268715179785183083 98238447403072769677774625)
  ·
    refine ⟨73678835552304577258330969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98238447403072769677774625 73678835552304577258330969)
    ·
      refine ⟨55259126664228432943748227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73678835552304577258330969 55259126664228432943748227)
      ·
        refine ⟨82888689996342649415622341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55259126664228432943748227 82888689996342649415622341)
        ·
          refine ⟨15541629374314246765429189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82888689996342649415622341 15541629374314246765429189)
          ·
            refine ⟨2914055507683921268517973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15541629374314246765429189 2914055507683921268517973)
            ·
              refine ⟨34149087980670952365445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2914055507683921268517973 34149087980670952365445)
              ·
                rfl

theorem cell22_2693457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 8].length) (baseStart_2693457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693457 prefixEnd_2693457 := by exact prefixLift 2693457
  have htrace : WordTrace (prefixWord ++ tailWord_2693457) baseStart_2693457 baseEnd_2693457 := by
    simpa [prefixWord, tailWord_2693457, baseEnd_2693457] using wordTrace_append hprefix tailTrace_2693457
  have hstable : (prefixWord ++ tailWord_2693457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693457).length < 2 ^ (prefixWord ++ tailWord_2693457).sum := by decide
  have hdescent : baseEnd_2693457 < baseStart_2693457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693474 : List Nat := [3, 3, 2, 1, 1, 3, 2, 7]
def baseStart_2693474 : Nat := 118140960795 + 2693474 * 2 ^ 59
def prefixEnd_2693474 : Nat := 4983230072969 + 3 ^ 40 * 2693474 * 2
def baseEnd_2693474 : Nat := 102447910547281481799107

theorem tailTrace_2693474 : CollatzResearch.WordTrace tailWord_2693474 prefixEnd_2693474 102447910547281481799107 := by
  unfold tailWord_2693474
  simp only [CollatzResearch.WordTrace]
  refine ⟨24559766861002795395285869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65492711629340787720762317 24559766861002795395285869)
  ·
    refine ⟨9209912572876048273232201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24559766861002795395285869 9209912572876048273232201)
    ·
      refine ⟨6907434429657036204924151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9209912572876048273232201 6907434429657036204924151)
      ·
        refine ⟨10361151644485554307386227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6907434429657036204924151 10361151644485554307386227)
        ·
          refine ⟨15541727466728331461079341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10361151644485554307386227 15541727466728331461079341)
          ·
            refine ⟨5828147800023124297904753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15541727466728331461079341 5828147800023124297904753)
            ·
              refine ⟨4371110850017343223428565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5828147800023124297904753 4371110850017343223428565)
              ·
                refine ⟨102447910547281481799107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4371110850017343223428565 102447910547281481799107)
                ·
                  rfl

theorem cell22_2693474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 7].length) (baseStart_2693474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693474 prefixEnd_2693474 := by exact prefixLift 2693474
  have htrace : WordTrace (prefixWord ++ tailWord_2693474) baseStart_2693474 baseEnd_2693474 := by
    simpa [prefixWord, tailWord_2693474, baseEnd_2693474] using wordTrace_append hprefix tailTrace_2693474
  have hstable : (prefixWord ++ tailWord_2693474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693474).length < 2 ^ (prefixWord ++ tailWord_2693474).sum := by decide
  have hdescent : baseEnd_2693474 < baseStart_2693474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693592 : List Nat := [2, 1, 2, 2, 2, 1, 1, 11]
def baseStart_2693592 : Nat := 118140960795 + 2693592 * 2 ^ 59
def prefixEnd_2693592 : Nat := 4983230072969 + 3 ^ 40 * 2693592 * 2
def baseEnd_2693592 : Nat := 102452398748557817971289

theorem tailTrace_2693592 : CollatzResearch.WordTrace tailWord_2693592 prefixEnd_2693592 102452398748557817971289 := by
  unfold tailWord_2693592
  simp only [CollatzResearch.WordTrace]
  refine ⟨49121685628791843866969515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65495580838389125155959353 49121685628791843866969515)
  ·
    refine ⟨73682528443187765800454273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49121685628791843866969515 73682528443187765800454273)
    ·
      refine ⟨55261896332390824350340705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73682528443187765800454273 55261896332390824350340705)
      ·
        refine ⟨41446422249293118262755529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55261896332390824350340705 41446422249293118262755529)
        ·
          refine ⟨31084816686969838697066647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41446422249293118262755529 31084816686969838697066647)
          ·
            refine ⟨46627225030454758045599971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31084816686969838697066647 46627225030454758045599971)
            ·
              refine ⟨69940837545682137068399957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46627225030454758045599971 69940837545682137068399957)
              ·
                refine ⟨102452398748557817971289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 69940837545682137068399957 102452398748557817971289)
                ·
                  rfl

theorem cell22_2693592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 11].length) (baseStart_2693592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693592 prefixEnd_2693592 := by exact prefixLift 2693592
  have htrace : WordTrace (prefixWord ++ tailWord_2693592) baseStart_2693592 baseEnd_2693592 := by
    simpa [prefixWord, tailWord_2693592, baseEnd_2693592] using wordTrace_append hprefix tailTrace_2693592
  have hstable : (prefixWord ++ tailWord_2693592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693592).length < 2 ^ (prefixWord ++ tailWord_2693592).sum := by decide
  have hdescent : baseEnd_2693592 < baseStart_2693592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693692 : List Nat := [2, 2, 2, 2, 3, 3, 2, 2, 1, 3]
def baseStart_2693692 : Nat := 118140960795 + 2693692 * 2 ^ 59
def prefixEnd_2693692 : Nat := 4983230072969 + 3 ^ 40 * 2693692 * 2
def baseEnd_2693692 : Nat := 922105820780653434241295

theorem tailTrace_2693692 : CollatzResearch.WordTrace tailWord_2693692 prefixEnd_2693692 922105820780653434241295 := by
  unfold tailWord_2693692
  simp only [CollatzResearch.WordTrace]
  refine ⟨49123509278610702406289665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65498012371480936541719553 49123509278610702406289665)
  ·
    refine ⟨36842631958958026804717249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49123509278610702406289665 36842631958958026804717249)
    ·
      refine ⟨27631973969218520103537937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36842631958958026804717249 27631973969218520103537937)
      ·
        refine ⟨20723980476913890077653453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27631973969218520103537937 20723980476913890077653453)
        ·
          refine ⟨7771492678842708779120045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20723980476913890077653453 7771492678842708779120045)
          ·
            refine ⟨2914309754566015792170017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7771492678842708779120045 2914309754566015792170017)
            ·
              refine ⟨2185732315924511844127513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2914309754566015792170017 2185732315924511844127513)
              ·
                refine ⟨1639299236943383883095635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2185732315924511844127513 1639299236943383883095635)
                ·
                  refine ⟨2458948855415075824643453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1639299236943383883095635 2458948855415075824643453)
                  ·
                    refine ⟨922105820780653434241295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2458948855415075824643453 922105820780653434241295)
                    ·
                      rfl

theorem cell22_2693692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_2693692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693692 prefixEnd_2693692 := by exact prefixLift 2693692
  have htrace : WordTrace (prefixWord ++ tailWord_2693692) baseStart_2693692 baseEnd_2693692 := by
    simpa [prefixWord, tailWord_2693692, baseEnd_2693692] using wordTrace_append hprefix tailTrace_2693692
  have hstable : (prefixWord ++ tailWord_2693692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693692).length < 2 ^ (prefixWord ++ tailWord_2693692).sum := by decide
  have hdescent : baseEnd_2693692 < baseStart_2693692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693716 : List Nat := [2, 4, 1, 1, 1, 4, 1, 2, 6]
def baseStart_2693716 : Nat := 118140960795 + 2693716 * 2 ^ 59
def prefixEnd_2693716 : Nat := 4983230072969 + 3 ^ 40 * 2693716 * 2
def baseEnd_2693716 : Nat := 307371345490375123880407

theorem tailTrace_2693716 : CollatzResearch.WordTrace tailWord_2693716 prefixEnd_2693716 307371345490375123880407 := by
  unfold tailWord_2693716
  simp only [CollatzResearch.WordTrace]
  refine ⟨49123946954567228455726501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65498595939422971274302001 49123946954567228455726501)
  ·
    refine ⟨9210740053981355335448719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49123946954567228455726501 9210740053981355335448719)
    ·
      refine ⟨13816110080972033003173079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9210740053981355335448719 13816110080972033003173079)
      ·
        refine ⟨20724165121458049504759619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13816110080972033003173079 20724165121458049504759619)
        ·
          refine ⟨31086247682187074257139429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20724165121458049504759619 31086247682187074257139429)
          ·
            refine ⟨5828671440410076423213643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31086247682187074257139429 5828671440410076423213643)
            ·
              refine ⟨8743007160615114634820465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5828671440410076423213643 8743007160615114634820465)
              ·
                refine ⟨6557255370461335976115349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8743007160615114634820465 6557255370461335976115349)
                ·
                  refine ⟨307371345490375123880407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6557255370461335976115349 307371345490375123880407)
                  ·
                    rfl

theorem cell22_2693716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_2693716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693716 prefixEnd_2693716 := by exact prefixLift 2693716
  have htrace : WordTrace (prefixWord ++ tailWord_2693716) baseStart_2693716 baseEnd_2693716 := by
    simpa [prefixWord, tailWord_2693716, baseEnd_2693716] using wordTrace_append hprefix tailTrace_2693716
  have hstable : (prefixWord ++ tailWord_2693716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693716).length < 2 ^ (prefixWord ++ tailWord_2693716).sum := by decide
  have hdescent : baseEnd_2693716 < baseStart_2693716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693726 : List Nat := [4, 4, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_2693726 : Nat := 118140960795 + 2693726 * 2 ^ 59
def prefixEnd_2693726 : Nat := 4983230072969 + 3 ^ 40 * 2693726 * 2
def baseEnd_2693726 : Nat := 922117459675488678891191

theorem tailTrace_2693726 : CollatzResearch.WordTrace tailWord_2693726 prefixEnd_2693726 922117459675488678891191 := by
  unfold tailWord_2693726
  simp only [CollatzResearch.WordTrace]
  refine ⟨12281032329887278577414629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65498839092732152412878021 12281032329887278577414629)
  ·
    refine ⟨2302693561853864733265243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12281032329887278577414629 2302693561853864733265243)
    ·
      refine ⟨3454040342780797099897865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2302693561853864733265243 3454040342780797099897865)
      ·
        refine ⟨2590530257085597824923399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3454040342780797099897865 2590530257085597824923399)
        ·
          refine ⟨3885795385628396737385099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2590530257085597824923399 3885795385628396737385099)
          ·
            refine ⟨5828693078442595106077649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3885795385628396737385099 5828693078442595106077649)
            ·
              refine ⟨4371519808831946329558237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5828693078442595106077649 4371519808831946329558237)
              ·
                refine ⟨1639319928311979873584339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4371519808831946329558237 1639319928311979873584339)
                ·
                  refine ⟨2458979892467969810376509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1639319928311979873584339 2458979892467969810376509)
                  ·
                    refine ⟨922117459675488678891191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2458979892467969810376509 922117459675488678891191)
                    ·
                      rfl

theorem cell22_2693726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_2693726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693726 prefixEnd_2693726 := by exact prefixLift 2693726
  have htrace : WordTrace (prefixWord ++ tailWord_2693726) baseStart_2693726 baseEnd_2693726 := by
    simpa [prefixWord, tailWord_2693726, baseEnd_2693726] using wordTrace_append hprefix tailTrace_2693726
  have hstable : (prefixWord ++ tailWord_2693726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693726).length < 2 ^ (prefixWord ++ tailWord_2693726).sum := by decide
  have hdescent : baseEnd_2693726 < baseStart_2693726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693731 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 4, 3]
def baseStart_2693731 : Nat := 118140960795 + 2693731 * 2 ^ 59
def prefixEnd_2693731 : Nat := 4983230072969 + 3 ^ 40 * 2693731 * 2
def baseEnd_2693731 : Nat := 922119171277670332516175

theorem tailTrace_2693731 : CollatzResearch.WordTrace tailWord_2693731 prefixEnd_2693731 922119171277670332516175 := by
  unfold tailWord_2693731
  simp only [CollatzResearch.WordTrace]
  refine ⟨98248441004080114473249047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65498960669386742982166031 98248441004080114473249047)
  ·
    refine ⟨147372661506120171709873571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98248441004080114473249047 147372661506120171709873571)
    ·
      refine ⟨221058992259180257564810357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147372661506120171709873571 221058992259180257564810357)
      ·
        refine ⟨20724280524298149146700971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 221058992259180257564810357 20724280524298149146700971)
        ·
          refine ⟨31086420786447223720051457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20724280524298149146700971 31086420786447223720051457)
          ·
            refine ⟨23314815589835417790038593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31086420786447223720051457 23314815589835417790038593)
            ·
              refine ⟨17486111692376563342528945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23314815589835417790038593 17486111692376563342528945)
              ·
                refine ⟨13114583769282422506896709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17486111692376563342528945 13114583769282422506896709)
                ·
                  refine ⟨2458984456740454220043133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13114583769282422506896709 2458984456740454220043133)
                  ·
                    refine ⟨922119171277670332516175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2458984456740454220043133 922119171277670332516175)
                    ·
                      rfl

theorem cell22_2693731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 3].length) (baseStart_2693731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693731 prefixEnd_2693731 := by exact prefixLift 2693731
  have htrace : WordTrace (prefixWord ++ tailWord_2693731) baseStart_2693731 baseEnd_2693731 := by
    simpa [prefixWord, tailWord_2693731, baseEnd_2693731] using wordTrace_append hprefix tailTrace_2693731
  have hstable : (prefixWord ++ tailWord_2693731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693731).length < 2 ^ (prefixWord ++ tailWord_2693731).sum := by decide
  have hdescent : baseEnd_2693731 < baseStart_2693731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693765 : List Nat := [1, 3, 1, 1, 4, 3, 3, 1, 2, 3]
def baseStart_2693765 : Nat := 118140960795 + 2693765 * 2 ^ 59
def prefixEnd_2693765 : Nat := 4983230072969 + 3 ^ 40 * 2693765 * 2
def baseEnd_2693765 : Nat := 922130810172505577166071

theorem tailTrace_2693765 : CollatzResearch.WordTrace tailWord_2693765 prefixEnd_2693765 922130810172505577166071 := by
  unfold tailWord_2693765
  simp only [CollatzResearch.WordTrace]
  refine ⟨98249681085956938279986749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65499787390637958853324499 98249681085956938279986749)
  ·
    refine ⟨36843630407233851854995031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98249681085956938279986749 36843630407233851854995031)
    ·
      refine ⟨55265445610850777782492547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36843630407233851854995031 55265445610850777782492547)
      ·
        refine ⟨82898168416276166673738821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55265445610850777782492547 82898168416276166673738821)
        ·
          refine ⟨15543406578051781251326029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82898168416276166673738821 15543406578051781251326029)
          ·
            refine ⟨5828777466769417969247261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15543406578051781251326029 5828777466769417969247261)
            ·
              refine ⟨2185791550038531738467723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5828777466769417969247261 2185791550038531738467723)
              ·
                refine ⟨3278687325057797607701585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185791550038531738467723 3278687325057797607701585)
                ·
                  refine ⟨2459015493793348205776189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3278687325057797607701585 2459015493793348205776189)
                  ·
                    refine ⟨922130810172505577166071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2459015493793348205776189 922130810172505577166071)
                    ·
                      rfl

theorem cell22_2693765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 2, 3].length) (baseStart_2693765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693765 prefixEnd_2693765 := by exact prefixLift 2693765
  have htrace : WordTrace (prefixWord ++ tailWord_2693765) baseStart_2693765 baseEnd_2693765 := by
    simpa [prefixWord, tailWord_2693765, baseEnd_2693765] using wordTrace_append hprefix tailTrace_2693765
  have hstable : (prefixWord ++ tailWord_2693765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693765).length < 2 ^ (prefixWord ++ tailWord_2693765).sum := by decide
  have hdescent : baseEnd_2693765 < baseStart_2693765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693778 : List Nat := [3, 2, 3, 1, 2, 1, 4, 6]
def baseStart_2693778 : Nat := 118140960795 + 2693778 * 2 ^ 59
def prefixEnd_2693778 : Nat := 4983230072969 + 3 ^ 40 * 2693778 * 2
def baseEnd_2693778 : Nat := 102459473370908652954559

theorem tailTrace_2693778 : CollatzResearch.WordTrace tailWord_2693778 prefixEnd_2693778 102459473370908652954559 := by
  unfold tailWord_2693778
  simp only [CollatzResearch.WordTrace]
  refine ⟨24562538808727460375052497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65500103489939894333473325 24562538808727460375052497)
  ·
    refine ⟨18421904106545595281289373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24562538808727460375052497 18421904106545595281289373)
    ·
      refine ⟨6908214039954598230483515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18421904106545595281289373 6908214039954598230483515)
      ·
        refine ⟨10362321059931897345725273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6908214039954598230483515 10362321059931897345725273)
        ·
          refine ⟨7771740794948923009293955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10362321059931897345725273 7771740794948923009293955)
          ·
            refine ⟨11657611192423384513940933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7771740794948923009293955 11657611192423384513940933)
            ·
              refine ⟨2185802098579384596363925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11657611192423384513940933 2185802098579384596363925)
              ·
                refine ⟨102459473370908652954559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2185802098579384596363925 102459473370908652954559)
                ·
                  rfl

theorem cell22_2693778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 6].length) (baseStart_2693778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693778 prefixEnd_2693778 := by exact prefixLift 2693778
  have htrace : WordTrace (prefixWord ++ tailWord_2693778) baseStart_2693778 baseEnd_2693778 := by
    simpa [prefixWord, tailWord_2693778, baseEnd_2693778] using wordTrace_append hprefix tailTrace_2693778
  have hstable : (prefixWord ++ tailWord_2693778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693778).length < 2 ^ (prefixWord ++ tailWord_2693778).sum := by decide
  have hdescent : baseEnd_2693778 < baseStart_2693778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693819 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 1, 10]
def baseStart_2693819 : Nat := 118140960795 + 2693819 * 2 ^ 59
def prefixEnd_2693819 : Nat := 4983230072969 + 3 ^ 40 * 2693819 * 2
def baseEnd_2693819 : Nat := 922149295476067436315905

theorem tailTrace_2693819 : CollatzResearch.WordTrace tailWord_2693819 prefixEnd_2693819 922149295476067436315905 := by
  unfold tailWord_2693819
  simp only [CollatzResearch.WordTrace]
  refine ⟨98251650627761305502452511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65501100418507537001635007 98251650627761305502452511)
  ·
    refine ⟨147377475941641958253678767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98251650627761305502452511 147377475941641958253678767)
    ·
      refine ⟨221066213912462937380518151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147377475941641958253678767 221066213912462937380518151)
      ·
        refine ⟨331599320868694406070777227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221066213912462937380518151 331599320868694406070777227)
        ·
          refine ⟨497398981303041609106165841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331599320868694406070777227 497398981303041609106165841)
          ·
            refine ⟨373049235977281206829624381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497398981303041609106165841 373049235977281206829624381)
            ·
              refine ⟨139893463491480452561109143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 373049235977281206829624381 139893463491480452561109143)
              ·
                refine ⟨209840195237220678841663715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139893463491480452561109143 209840195237220678841663715)
                ·
                  refine ⟨314760292855831018262495573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209840195237220678841663715 314760292855831018262495573)
                  ·
                    refine ⟨922149295476067436315905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 314760292855831018262495573 922149295476067436315905)
                    ·
                      rfl

theorem cell22_2693819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 10].length) (baseStart_2693819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693819 prefixEnd_2693819 := by exact prefixLift 2693819
  have htrace : WordTrace (prefixWord ++ tailWord_2693819) baseStart_2693819 baseEnd_2693819 := by
    simpa [prefixWord, tailWord_2693819, baseEnd_2693819] using wordTrace_append hprefix tailTrace_2693819
  have hstable : (prefixWord ++ tailWord_2693819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693819).length < 2 ^ (prefixWord ++ tailWord_2693819).sum := by decide
  have hdescent : baseEnd_2693819 < baseStart_2693819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693823 : List Nat := [1, 1, 2, 2, 2, 4, 4, 1, 5]
def baseStart_2693823 : Nat := 118140960795 + 2693823 * 2 ^ 59
def prefixEnd_2693823 : Nat := 4983230072969 + 3 ^ 40 * 2693823 * 2
def baseEnd_2693823 : Nat := 307383554919270919738631

theorem tailTrace_2693823 : CollatzResearch.WordTrace tailWord_2693823 prefixEnd_2693823 307383554919270919738631 := by
  unfold tailWord_2693823
  simp only [CollatzResearch.WordTrace]
  refine ⟨98251796519746814185598123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65501197679831209457065415 98251796519746814185598123)
  ·
    refine ⟨147377694779620221278397185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98251796519746814185598123 147377694779620221278397185)
    ·
      refine ⟨110533271084715165958797889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147377694779620221278397185 110533271084715165958797889)
      ·
        refine ⟨82899953313536374469098417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110533271084715165958797889 82899953313536374469098417)
        ·
          refine ⟨62174964985152280851823813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82899953313536374469098417 62174964985152280851823813)
          ·
            refine ⟨11657805934716052659716965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62174964985152280851823813 11657805934716052659716965)
            ·
              refine ⟨2185838612759259873696931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11657805934716052659716965 2185838612759259873696931)
              ·
                refine ⟨3278757919138889810545397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185838612759259873696931 3278757919138889810545397)
                ·
                  refine ⟨307383554919270919738631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3278757919138889810545397 307383554919270919738631)
                  ·
                    rfl

theorem cell22_2693823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 5].length) (baseStart_2693823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693823 prefixEnd_2693823 := by exact prefixLift 2693823
  have htrace : WordTrace (prefixWord ++ tailWord_2693823) baseStart_2693823 baseEnd_2693823 := by
    simpa [prefixWord, tailWord_2693823, baseEnd_2693823] using wordTrace_append hprefix tailTrace_2693823
  have hstable : (prefixWord ++ tailWord_2693823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693823).length < 2 ^ (prefixWord ++ tailWord_2693823).sum := by decide
  have hdescent : baseEnd_2693823 < baseStart_2693823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693866 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 5, 5]
def baseStart_2693866 : Nat := 118140960795 + 2693866 * 2 ^ 59
def prefixEnd_2693866 : Nat := 4983230072969 + 3 ^ 40 * 2693866 * 2
def baseEnd_2693866 : Nat := 922165384536574980390761

theorem tailTrace_2693866 : CollatzResearch.WordTrace tailWord_2693866 prefixEnd_2693866 922165384536574980390761 := by
  unfold tailWord_2693866
  simp only [CollatzResearch.WordTrace]
  refine ⟨24563341214647758132353363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65502243239060688352942301 24563341214647758132353363)
  ·
    refine ⟨36845011821971637198530045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24563341214647758132353363 36845011821971637198530045)
    ·
      refine ⟨13816879433239363949448767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36845011821971637198530045 13816879433239363949448767)
      ·
        refine ⟨20725319149859045924173151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13816879433239363949448767 20725319149859045924173151)
        ·
          refine ⟨31087978724788568886259727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20725319149859045924173151 31087978724788568886259727)
          ·
            refine ⟨46631968087182853329389591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31087978724788568886259727 46631968087182853329389591)
            ·
              refine ⟨69947952130774279994084387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46631968087182853329389591 69947952130774279994084387)
              ·
                refine ⟨104921928196161419991126581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69947952130774279994084387 104921928196161419991126581)
                ·
                  refine ⟨9836430768390133124168117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104921928196161419991126581 9836430768390133124168117)
                  ·
                    refine ⟨922165384536574980390761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9836430768390133124168117 922165384536574980390761)
                    ·
                      rfl

theorem cell22_2693866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_2693866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693866 prefixEnd_2693866 := by exact prefixLift 2693866
  have htrace : WordTrace (prefixWord ++ tailWord_2693866) baseStart_2693866 baseEnd_2693866 := by
    simpa [prefixWord, tailWord_2693866, baseEnd_2693866] using wordTrace_append hprefix tailTrace_2693866
  have hstable : (prefixWord ++ tailWord_2693866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693866).length < 2 ^ (prefixWord ++ tailWord_2693866).sum := by decide
  have hdescent : baseEnd_2693866 < baseStart_2693866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693881 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 4, 4]
def baseStart_2693881 : Nat := 118140960795 + 2693881 * 2 ^ 59
def prefixEnd_2693881 : Nat := 4983230072969 + 3 ^ 40 * 2693881 * 2
def baseEnd_2693881 : Nat := 922170519343119941265715

theorem tailTrace_2693881 : CollatzResearch.WordTrace tailWord_2693881 prefixEnd_2693881 922170519343119941265715 := by
  unfold tailWord_2693881
  simp only [CollatzResearch.WordTrace]
  refine ⟨98253911953536690091209497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65502607969024460060806331 98253911953536690091209497)
  ·
    refine ⟨73690433965152517568407123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98253911953536690091209497 73690433965152517568407123)
    ·
      refine ⟨110535650947728776352610685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73690433965152517568407123 110535650947728776352610685)
      ·
        refine ⟨41450869105398291132229007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110535650947728776352610685 41450869105398291132229007)
        ·
          refine ⟨62176303658097436698343511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41450869105398291132229007 62176303658097436698343511)
          ·
            refine ⟨93264455487146155047515267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62176303658097436698343511 93264455487146155047515267)
            ·
              refine ⟨139896683230719232571272901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93264455487146155047515267 139896683230719232571272901)
              ·
                refine ⟨26230628105759856107113669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139896683230719232571272901 26230628105759856107113669)
                ·
                  refine ⟨4918242769829973020083813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26230628105759856107113669 4918242769829973020083813)
                  ·
                    refine ⟨922170519343119941265715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4918242769829973020083813 922170519343119941265715)
                    ·
                      rfl

theorem cell22_2693881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_2693881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693881 prefixEnd_2693881 := by exact prefixLift 2693881
  have htrace : WordTrace (prefixWord ++ tailWord_2693881) baseStart_2693881 baseEnd_2693881 := by
    simpa [prefixWord, tailWord_2693881, baseEnd_2693881] using wordTrace_append hprefix tailTrace_2693881
  have hstable : (prefixWord ++ tailWord_2693881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693881).length < 2 ^ (prefixWord ++ tailWord_2693881).sum := by decide
  have hdescent : baseEnd_2693881 < baseStart_2693881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693917 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 4, 3]
def baseStart_2693917 : Nat := 118140960795 + 2693917 * 2 ^ 59
def prefixEnd_2693917 : Nat := 4983230072969 + 3 ^ 40 * 2693917 * 2
def baseEnd_2693917 : Nat := 922182842878827847365605

theorem tailTrace_2693917 : CollatzResearch.WordTrace tailWord_2693917 prefixEnd_2693917 922182842878827847365605 := by
  unfold tailWord_2693917
  simp only [CollatzResearch.WordTrace]
  refine ⟨98255224981406268239520005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65503483320937512159680003 98255224981406268239520005)
  ·
    refine ⟨18422854684013675294910001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98255224981406268239520005 18422854684013675294910001)
    ·
      refine ⟨13817141013010256471182501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18422854684013675294910001 13817141013010256471182501)
      ·
        refine ⟨2590713939939423088346719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13817141013010256471182501 2590713939939423088346719)
        ·
          refine ⟨3886070909909134632520079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2590713939939423088346719 3886070909909134632520079)
          ·
            refine ⟨5829106364863701948780119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3886070909909134632520079 5829106364863701948780119)
            ·
              refine ⟨8743659547295552923170179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5829106364863701948780119 8743659547295552923170179)
              ·
                refine ⟨13115489320943329384755269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8743659547295552923170179 13115489320943329384755269)
                ·
                  refine ⟨2459154247676874259641613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13115489320943329384755269 2459154247676874259641613)
                  ·
                    refine ⟨922182842878827847365605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2459154247676874259641613 922182842878827847365605)
                    ·
                      rfl

theorem cell22_2693917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_2693917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693917 prefixEnd_2693917 := by exact prefixLift 2693917
  have htrace : WordTrace (prefixWord ++ tailWord_2693917) baseStart_2693917 baseEnd_2693917 := by
    simpa [prefixWord, tailWord_2693917, baseEnd_2693917] using wordTrace_append hprefix tailTrace_2693917
  have hstable : (prefixWord ++ tailWord_2693917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693917).length < 2 ^ (prefixWord ++ tailWord_2693917).sum := by decide
  have hdescent : baseEnd_2693917 < baseStart_2693917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693934 : List Nat := [4, 1, 3, 2, 1, 2, 3, 1, 2, 3]
def baseStart_2693934 : Nat := 118140960795 + 2693934 * 2 ^ 59
def prefixEnd_2693934 : Nat := 4983230072969 + 3 ^ 40 * 2693934 * 2
def baseEnd_2693934 : Nat := 922188662326245469690553

theorem tailTrace_2693934 : CollatzResearch.WordTrace tailWord_2693934 prefixEnd_2693934 922188662326245469690553 := by
  unfold tailWord_2693934
  simp only [CollatzResearch.WordTrace]
  refine ⟨12281980627793085017861107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65503896681563120095259237 12281980627793085017861107)
  ·
    refine ⟨18422970941689627526791661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12281980627793085017861107 18422970941689627526791661)
    ·
      refine ⟨6908614103133610322546873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18422970941689627526791661 6908614103133610322546873)
      ·
        refine ⟨5181460577350207741910155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6908614103133610322546873 5181460577350207741910155)
        ·
          refine ⟨7772190866025311612865233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5181460577350207741910155 7772190866025311612865233)
          ·
            refine ⟨5829143149518983709648925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7772190866025311612865233 5829143149518983709648925)
            ·
              refine ⟨2185928681069618891118347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5829143149518983709648925 2185928681069618891118347)
              ·
                refine ⟨3278893021604428336677521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185928681069618891118347 3278893021604428336677521)
                ·
                  refine ⟨2459169766203321252508141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3278893021604428336677521 2459169766203321252508141)
                  ·
                    refine ⟨922188662326245469690553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2459169766203321252508141 922188662326245469690553)
                    ·
                      rfl

theorem cell22_2693934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_2693934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693934 prefixEnd_2693934 := by exact prefixLift 2693934
  have htrace : WordTrace (prefixWord ++ tailWord_2693934) baseStart_2693934 baseEnd_2693934 := by
    simpa [prefixWord, tailWord_2693934, baseEnd_2693934] using wordTrace_append hprefix tailTrace_2693934
  have hstable : (prefixWord ++ tailWord_2693934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693934).length < 2 ^ (prefixWord ++ tailWord_2693934).sum := by decide
  have hdescent : baseEnd_2693934 < baseStart_2693934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693992 : List Nat := [2, 1, 4, 2, 1, 4, 2, 1, 5]
def baseStart_2693992 : Nat := 118140960795 + 2693992 * 2 ^ 59
def prefixEnd_2693992 : Nat := 4983230072969 + 3 ^ 40 * 2693992 * 2
def baseEnd_2693992 : Nat := 307402838970517550580125

theorem tailTrace_2693992 : CollatzResearch.WordTrace tailWord_2693992 prefixEnd_2693992 307402838970517550580125 := by
  unfold tailWord_2693992
  simp only [CollatzResearch.WordTrace]
  refine ⟨49128980228067278024250115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65505306970756370699000153 49128980228067278024250115)
  ·
    refine ⟨73693470342100917036375173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49128980228067278024250115 73693470342100917036375173)
    ·
      refine ⟨13817525689143921944320345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73693470342100917036375173 13817525689143921944320345)
      ·
        refine ⟨10363144266857941458240259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13817525689143921944320345 10363144266857941458240259)
        ·
          refine ⟨15544716400286912187360389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10363144266857941458240259 15544716400286912187360389)
          ·
            refine ⟨2914634325053796035130073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15544716400286912187360389 2914634325053796035130073)
            ·
              refine ⟨2185975743790347026347555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2914634325053796035130073 2185975743790347026347555)
              ·
                refine ⟨3278963615685520539521333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185975743790347026347555 3278963615685520539521333)
                ·
                  refine ⟨307402838970517550580125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3278963615685520539521333 307402838970517550580125)
                  ·
                    rfl

theorem cell22_2693992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 5].length) (baseStart_2693992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693992 prefixEnd_2693992 := by exact prefixLift 2693992
  have htrace : WordTrace (prefixWord ++ tailWord_2693992) baseStart_2693992 baseEnd_2693992 := by
    simpa [prefixWord, tailWord_2693992, baseEnd_2693992] using wordTrace_append hprefix tailTrace_2693992
  have hstable : (prefixWord ++ tailWord_2693992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693992).length < 2 ^ (prefixWord ++ tailWord_2693992).sum := by decide
  have hdescent : baseEnd_2693992 < baseStart_2693992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694005 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2694005 : Nat := 118140960795 + 2694005 * 2 ^ 59
def prefixEnd_2694005 : Nat := 4983230072969 + 3 ^ 40 * 2694005 * 2
def baseEnd_2694005 : Nat := 922212967077224951165335

theorem tailTrace_2694005 : CollatzResearch.WordTrace tailWord_2694005 prefixEnd_2694005 922212967077224951165335 := by
  unfold tailWord_2694005
  simp only [CollatzResearch.WordTrace]
  refine ⟨98258434605087459268723469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65505623070058306179148979 98258434605087459268723469)
  ·
    refine ⟨36846912976907797225771301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98258434605087459268723469 36846912976907797225771301)
    ·
      refine ⟨6908796183170211979832119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36846912976907797225771301 6908796183170211979832119)
      ·
        refine ⟨10363194274755317969748179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6908796183170211979832119 10363194274755317969748179)
        ·
          refine ⟨15544791412132976954622269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10363194274755317969748179 15544791412132976954622269)
          ·
            refine ⟨5829296779549866357983351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15544791412132976954622269 5829296779549866357983351)
            ·
              refine ⟨8743945169324799536975027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5829296779549866357983351 8743945169324799536975027)
              ·
                refine ⟨13115917753987199305462541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8743945169324799536975027 13115917753987199305462541)
                ·
                  refine ⟨4918469157745199739548453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13115917753987199305462541 4918469157745199739548453)
                  ·
                    refine ⟨922212967077224951165335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4918469157745199739548453 922212967077224951165335)
                    ·
                      rfl

theorem cell22_2694005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2694005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694005 prefixEnd_2694005 := by exact prefixLift 2694005
  have htrace : WordTrace (prefixWord ++ tailWord_2694005) baseStart_2694005 baseEnd_2694005 := by
    simpa [prefixWord, tailWord_2694005, baseEnd_2694005] using wordTrace_append hprefix tailTrace_2694005
  have hstable : (prefixWord ++ tailWord_2694005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694005).length < 2 ^ (prefixWord ++ tailWord_2694005).sum := by decide
  have hdescent : baseEnd_2694005 < baseStart_2694005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694020 : List Nat := [2, 3, 2, 1, 1, 1, 1, 7, 4]
def baseStart_2694020 : Nat := 118140960795 + 2694020 * 2 ^ 59
def prefixEnd_2694020 : Nat := 4983230072969 + 3 ^ 40 * 2694020 * 2
def baseEnd_2694020 : Nat := 307406033961256637346763

theorem tailTrace_2694020 : CollatzResearch.WordTrace tailWord_2694020 prefixEnd_2694020 307406033961256637346763 := by
  unfold tailWord_2694020
  simp only [CollatzResearch.WordTrace]
  refine ⟨49129490850016558415259757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65505987800022077887013009 49129490850016558415259757)
  ·
    refine ⟨18423559068756209405722409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49129490850016558415259757 18423559068756209405722409)
    ·
      refine ⟨13817669301567157054291807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18423559068756209405722409 13817669301567157054291807)
      ·
        refine ⟨20726503952350735581437711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13817669301567157054291807 20726503952350735581437711)
        ·
          refine ⟨31089755928526103372156567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20726503952350735581437711 31089755928526103372156567)
          ·
            refine ⟨46634633892789155058234851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31089755928526103372156567 46634633892789155058234851)
            ·
              refine ⟨69951950839183732587352277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46634633892789155058234851 69951950839183732587352277)
              ·
                refine ⟨1639498847793368732516069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 69951950839183732587352277 1639498847793368732516069)
                ·
                  refine ⟨307406033961256637346763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1639498847793368732516069 307406033961256637346763)
                  ·
                    rfl

theorem cell22_2694020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_2694020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694020 prefixEnd_2694020 := by exact prefixLift 2694020
  have htrace : WordTrace (prefixWord ++ tailWord_2694020) baseStart_2694020 baseEnd_2694020 := by
    simpa [prefixWord, tailWord_2694020, baseEnd_2694020] using wordTrace_append hprefix tailTrace_2694020
  have hstable : (prefixWord ++ tailWord_2694020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694020).length < 2 ^ (prefixWord ++ tailWord_2694020).sum := by decide
  have hdescent : baseEnd_2694020 < baseStart_2694020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694037 : List Nat := [1, 3, 2, 1, 1, 4, 4, 2, 4]
def baseStart_2694037 : Nat := 118140960795 + 2694037 * 2 ^ 59
def prefixEnd_2694037 : Nat := 4983230072969 + 3 ^ 40 * 2694037 * 2
def baseEnd_2694037 : Nat := 307407973777062511455079

theorem tailTrace_2694037 : CollatzResearch.WordTrace tailWord_2694037 prefixEnd_2694037 307407973777062511455079 := by
  unfold tailWord_2694037
  simp only [CollatzResearch.WordTrace]
  refine ⟨98259601740971528733888365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65506401160647685822592243 98259601740971528733888365)
  ·
    refine ⟨36847350652864323275208137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98259601740971528733888365 36847350652864323275208137)
    ·
      refine ⟨27635512989648242456406103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36847350652864323275208137 27635512989648242456406103)
      ·
        refine ⟨41453269484472363684609155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27635512989648242456406103 41453269484472363684609155)
        ·
          refine ⟨62179904226708545526913733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41453269484472363684609155 62179904226708545526913733)
          ·
            refine ⟨11658732042507852286296325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62179904226708545526913733 11658732042507852286296325)
            ·
              refine ⟨2186012257970222303680561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11658732042507852286296325 2186012257970222303680561)
              ·
                refine ⟨1639509193477666727760421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2186012257970222303680561 1639509193477666727760421)
                ·
                  refine ⟨307407973777062511455079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1639509193477666727760421 307407973777062511455079)
                  ·
                    rfl

theorem cell22_2694037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_2694037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694037 prefixEnd_2694037 := by exact prefixLift 2694037
  have htrace : WordTrace (prefixWord ++ tailWord_2694037) baseStart_2694037 baseEnd_2694037 := by
    simpa [prefixWord, tailWord_2694037, baseEnd_2694037] using wordTrace_append hprefix tailTrace_2694037
  have hstable : (prefixWord ++ tailWord_2694037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694037).length < 2 ^ (prefixWord ++ tailWord_2694037).sum := by decide
  have hdescent : baseEnd_2694037 < baseStart_2694037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694048 : List Nat := [2, 1, 1, 4, 1, 1, 5, 7]
def baseStart_2694048 : Nat := 118140960795 + 2694048 * 2 ^ 59
def prefixEnd_2694048 : Nat := 4983230072969 + 3 ^ 40 * 2694048 * 2
def baseEnd_2694048 : Nat := 102469742983998574704467

theorem tailTrace_2694048 : CollatzResearch.WordTrace tailWord_2694048 prefixEnd_2694048 102469742983998574704467 := by
  unfold tailWord_2694048
  simp only [CollatzResearch.WordTrace]
  refine ⟨49130001471965838806269399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65506668629287785075025865 49130001471965838806269399)
  ·
    refine ⟨73695002207948758209404099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49130001471965838806269399 73695002207948758209404099)
    ·
      refine ⟨110542503311923137314106149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73695002207948758209404099 110542503311923137314106149)
      ·
        refine ⟨20726719370985588246394903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110542503311923137314106149 20726719370985588246394903)
        ·
          refine ⟨31090079056478382369592355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20726719370985588246394903 31090079056478382369592355)
          ·
            refine ⟨46635118584717573554388533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31090079056478382369592355 46635118584717573554388533)
            ·
              refine ⟨4372042367317272520723925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46635118584717573554388533 4372042367317272520723925)
              ·
                refine ⟨102469742983998574704467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4372042367317272520723925 102469742983998574704467)
                ·
                  rfl

theorem cell22_2694048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 7].length) (baseStart_2694048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694048 prefixEnd_2694048 := by exact prefixLift 2694048
  have htrace : WordTrace (prefixWord ++ tailWord_2694048) baseStart_2694048 baseEnd_2694048 := by
    simpa [prefixWord, tailWord_2694048, baseEnd_2694048] using wordTrace_append hprefix tailTrace_2694048
  have hstable : (prefixWord ++ tailWord_2694048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694048).length < 2 ^ (prefixWord ++ tailWord_2694048).sum := by decide
  have hdescent : baseEnd_2694048 < baseStart_2694048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694097 : List Nat := [1, 2, 2, 1, 2, 1, 3, 6, 1, 3]
def baseStart_2694097 : Nat := 118140960795 + 2694097 * 2 ^ 59
def prefixEnd_2694097 : Nat := 4983230072969 + 3 ^ 40 * 2694097 * 2
def baseEnd_2694097 : Nat := 922244460557367377865053

theorem tailTrace_2694097 : CollatzResearch.WordTrace tailWord_2694097 prefixEnd_2694097 922244460557367377865053 := by
  unfold tailWord_2694097
  simp only [CollatzResearch.WordTrace]
  refine ⟨98261790120754158981072545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65507860080502772654048363 98261790120754158981072545)
  ·
    refine ⟨73696342590565619235804409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98261790120754158981072545 73696342590565619235804409)
    ·
      refine ⟨55272256942924214426853307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73696342590565619235804409 55272256942924214426853307)
      ·
        refine ⟨82908385414386321640279961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55272256942924214426853307 82908385414386321640279961)
        ·
          refine ⟨62181289060789741230209971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82908385414386321640279961 62181289060789741230209971)
          ·
            refine ⟨93271933591184611845314957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62181289060789741230209971 93271933591184611845314957)
            ·
              refine ⟨34976975096694229441993109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93271933591184611845314957 34976975096694229441993109)
              ·
                refine ⟨1639545707657542005093427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34976975096694229441993109 1639545707657542005093427)
                ·
                  refine ⟨2459318561486313007640141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1639545707657542005093427 2459318561486313007640141)
                  ·
                    refine ⟨922244460557367377865053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2459318561486313007640141 922244460557367377865053)
                    ·
                      rfl

theorem cell22_2694097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 1, 3].length) (baseStart_2694097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694097 prefixEnd_2694097 := by exact prefixLift 2694097
  have htrace : WordTrace (prefixWord ++ tailWord_2694097) baseStart_2694097 baseEnd_2694097 := by
    simpa [prefixWord, tailWord_2694097, baseEnd_2694097] using wordTrace_append hprefix tailTrace_2694097
  have hstable : (prefixWord ++ tailWord_2694097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694097).length < 2 ^ (prefixWord ++ tailWord_2694097).sum := by decide
  have hdescent : baseEnd_2694097 < baseStart_2694097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694114 : List Nat := [3, 3, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2694114 : Nat := 118140960795 + 2694114 * 2 ^ 59
def prefixEnd_2694114 : Nat := 4983230072969 + 3 ^ 40 * 2694114 * 2
def baseEnd_2694114 : Nat := 922250280004785000190001

theorem tailTrace_2694114 : CollatzResearch.WordTrace tailWord_2694114 prefixEnd_2694114 922250280004785000190001 := by
  unfold tailWord_2694114
  simp only [CollatzResearch.WordTrace]
  refine ⟨24565602540423142721110349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65508273441128380589627597 24565602540423142721110349)
  ·
    refine ⟨9212100952658678520416381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24565602540423142721110349 9212100952658678520416381)
    ·
      refine ⟨3454537857247004445156143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9212100952658678520416381 3454537857247004445156143)
      ·
        refine ⟨5181806785870506667734215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3454537857247004445156143 5181806785870506667734215)
        ·
          refine ⟨7772710178805760001601323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5181806785870506667734215 7772710178805760001601323)
          ·
            refine ⟨11659065268208640002401985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7772710178805760001601323 11659065268208640002401985)
            ·
              refine ⟨8744298951156480001801489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11659065268208640002401985 8744298951156480001801489)
              ·
                refine ⟨6558224213367360001351117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8744298951156480001801489 6558224213367360001351117)
                ·
                  refine ⟨2459334080012760000506669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6558224213367360001351117 2459334080012760000506669)
                  ·
                    refine ⟨922250280004785000190001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2459334080012760000506669 922250280004785000190001)
                    ·
                      rfl

theorem cell22_2694114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2694114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694114 prefixEnd_2694114 := by exact prefixLift 2694114
  have htrace : WordTrace (prefixWord ++ tailWord_2694114) baseStart_2694114 baseEnd_2694114 := by
    simpa [prefixWord, tailWord_2694114, baseEnd_2694114] using wordTrace_append hprefix tailTrace_2694114
  have hstable : (prefixWord ++ tailWord_2694114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694114).length < 2 ^ (prefixWord ++ tailWord_2694114).sum := by decide
  have hdescent : baseEnd_2694114 < baseStart_2694114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694138 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 8]
def baseStart_2694138 : Nat := 118140960795 + 2694138 * 2 ^ 59
def prefixEnd_2694138 : Nat := 4983230072969 + 3 ^ 40 * 2694138 * 2
def baseEnd_2694138 : Nat := 307419498565085645863309

theorem tailTrace_2694138 : CollatzResearch.WordTrace tailWord_2694138 prefixEnd_2694138 307419498565085645863309 := by
  unfold tailWord_2694138
  simp only [CollatzResearch.WordTrace]
  refine ⟨24565821378401405745828767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65508857009070415322210045 24565821378401405745828767)
  ·
    refine ⟨36848732067602108618743151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24565821378401405745828767 36848732067602108618743151)
    ·
      refine ⟨55273098101403162928114727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36848732067602108618743151 55273098101403162928114727)
      ·
        refine ⟨82909647152104744392172091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55273098101403162928114727 82909647152104744392172091)
        ·
          refine ⟨124364470728157116588258137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82909647152104744392172091 124364470728157116588258137)
          ·
            refine ⟨93273353046117837441193603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124364470728157116588258137 93273353046117837441193603)
            ·
              refine ⟨139910029569176756161790405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93273353046117837441193603 139910029569176756161790405)
              ·
                refine ⟨26233130544220641780335701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139910029569176756161790405 26233130544220641780335701)
                ·
                  refine ⟨307419498565085645863309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26233130544220641780335701 307419498565085645863309)
                  ·
                    rfl

theorem cell22_2694138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_2694138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694138 prefixEnd_2694138 := by exact prefixLift 2694138
  have htrace : WordTrace (prefixWord ++ tailWord_2694138) baseStart_2694138 baseEnd_2694138 := by
    simpa [prefixWord, tailWord_2694138, baseEnd_2694138] using wordTrace_append hprefix tailTrace_2694138
  have hstable : (prefixWord ++ tailWord_2694138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694138).length < 2 ^ (prefixWord ++ tailWord_2694138).sum := by decide
  have hdescent : baseEnd_2694138 < baseStart_2694138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694155 : List Nat := [1, 1, 1, 1, 6, 2, 3, 1, 6]
def baseStart_2694155 : Nat := 118140960795 + 2694155 * 2 ^ 59
def prefixEnd_2694155 : Nat := 4983230072969 + 3 ^ 40 * 2694155 * 2
def baseEnd_2694155 : Nat := 307421438380891519971625

theorem tailTrace_2694155 : CollatzResearch.WordTrace tailWord_2694155 prefixEnd_2694155 307421438380891519971625 := by
  unfold tailWord_2694155
  simp only [CollatzResearch.WordTrace]
  refine ⟨98263905554544034886683919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65509270369696023257789279 98263905554544034886683919)
  ·
    refine ⟨147395858331816052330025879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98263905554544034886683919 147395858331816052330025879)
    ·
      refine ⟨221093787497724078495038819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147395858331816052330025879 221093787497724078495038819)
      ·
        refine ⟨331640681246586117742558229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221093787497724078495038819 331640681246586117742558229)
        ·
          refine ⟨15545656933433724269182417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 331640681246586117742558229 15545656933433724269182417)
          ·
            refine ⟨11659242700075293201886813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15545656933433724269182417 11659242700075293201886813)
            ·
              refine ⟨4372216012528234950707555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11659242700075293201886813 4372216012528234950707555)
              ·
                refine ⟨6558324018792352426061333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4372216012528234950707555 6558324018792352426061333)
                ·
                  refine ⟨307421438380891519971625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6558324018792352426061333 307421438380891519971625)
                  ·
                    rfl

theorem cell22_2694155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 6].length) (baseStart_2694155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694155 prefixEnd_2694155 := by exact prefixLift 2694155
  have htrace : WordTrace (prefixWord ++ tailWord_2694155) baseStart_2694155 baseEnd_2694155 := by
    simpa [prefixWord, tailWord_2694155, baseEnd_2694155] using wordTrace_append hprefix tailTrace_2694155
  have hstable : (prefixWord ++ tailWord_2694155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694155).length < 2 ^ (prefixWord ++ tailWord_2694155).sum := by decide
  have hdescent : baseEnd_2694155 < baseStart_2694155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694170 : List Nat := [3, 1, 1, 3, 1, 2, 2, 3, 1, 5]
def baseStart_2694170 : Nat := 118140960795 + 2694170 * 2 ^ 59
def prefixEnd_2694170 : Nat := 4983230072969 + 3 ^ 40 * 2694170 * 2
def baseEnd_2694170 : Nat := 922269449949219520789829

theorem tailTrace_2694170 : CollatzResearch.WordTrace tailWord_2694170 prefixEnd_2694170 922269449949219520789829 := by
  unfold tailWord_2694170
  simp only [CollatzResearch.WordTrace]
  refine ⟨24566113162372423112119991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65509635099659794965653309 24566113162372423112119991)
  ·
    refine ⟨36849169743558634668179987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24566113162372423112119991 36849169743558634668179987)
    ·
      refine ⟨55273754615337952002269981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36849169743558634668179987 55273754615337952002269981)
      ·
        refine ⟨20727657980751732000851243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55273754615337952002269981 20727657980751732000851243)
        ·
          refine ⟨31091486971127598001276865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20727657980751732000851243 31091486971127598001276865)
          ·
            refine ⟨23318615228345698500957649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31091486971127598001276865 23318615228345698500957649)
            ·
              refine ⟨17488961421259273875718237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23318615228345698500957649 17488961421259273875718237)
              ·
                refine ⟨6558360532972227703394339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17488961421259273875718237 6558360532972227703394339)
                ·
                  refine ⟨9837540799458341555091509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6558360532972227703394339 9837540799458341555091509)
                  ·
                    refine ⟨922269449949219520789829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9837540799458341555091509 922269449949219520789829)
                    ·
                      rfl

theorem cell22_2694170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_2694170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694170 prefixEnd_2694170 := by exact prefixLift 2694170
  have htrace : WordTrace (prefixWord ++ tailWord_2694170) baseStart_2694170 baseEnd_2694170 := by
    simpa [prefixWord, tailWord_2694170, baseEnd_2694170] using wordTrace_append hprefix tailTrace_2694170
  have hstable : (prefixWord ++ tailWord_2694170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694170).length < 2 ^ (prefixWord ++ tailWord_2694170).sum := by decide
  have hdescent : baseEnd_2694170 < baseStart_2694170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694204 : List Nat := [2, 2, 2, 2, 2, 3, 2, 2, 2, 3]
def baseStart_2694204 : Nat := 118140960795 + 2694204 * 2 ^ 59
def prefixEnd_2694204 : Nat := 4983230072969 + 3 ^ 40 * 2694204 * 2
def baseEnd_2694204 : Nat := 922281088844054765439725

theorem tailTrace_2694204 : CollatzResearch.WordTrace tailWord_2694204 prefixEnd_2694204 922281088844054765439725 := by
  unfold tailWord_2694204
  simp only [CollatzResearch.WordTrace]
  refine ⟨49132846365683258127608833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65510461820911010836811777 49132846365683258127608833)
  ·
    refine ⟨36849634774262443595706625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49132846365683258127608833 36849634774262443595706625)
    ·
      refine ⟨27637226080696832696779969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36849634774262443595706625 27637226080696832696779969)
      ·
        refine ⟨20727919560522624522584977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27637226080696832696779969 20727919560522624522584977)
        ·
          refine ⟨15545939670391968391938733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20727919560522624522584977 15545939670391968391938733)
          ·
            refine ⟨5829727376396988146977025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15545939670391968391938733 5829727376396988146977025)
            ·
              refine ⟨4372295532297741110232769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5829727376396988146977025 4372295532297741110232769)
              ·
                refine ⟨3279221649223305832674577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4372295532297741110232769 3279221649223305832674577)
                ·
                  refine ⟨2459416236917479374505933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3279221649223305832674577 2459416236917479374505933)
                  ·
                    refine ⟨922281088844054765439725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2459416236917479374505933 922281088844054765439725)
                    ·
                      rfl

theorem cell22_2694204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_2694204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694204 prefixEnd_2694204 := by exact prefixLift 2694204
  have htrace : WordTrace (prefixWord ++ tailWord_2694204) baseStart_2694204 baseEnd_2694204 := by
    simpa [prefixWord, tailWord_2694204, baseEnd_2694204] using wordTrace_append hprefix tailTrace_2694204
  have hstable : (prefixWord ++ tailWord_2694204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694204).length < 2 ^ (prefixWord ++ tailWord_2694204).sum := by decide
  have hdescent : baseEnd_2694204 < baseStart_2694204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694206 : List Nat := [4, 2, 1, 3, 1, 1, 4, 2, 4]
def baseStart_2694206 : Nat := 118140960795 + 2694206 * 2 ^ 59
def prefixEnd_2694206 : Nat := 4983230072969 + 3 ^ 40 * 2694206 * 2
def baseEnd_2694206 : Nat := 307427257828309142296573

theorem tailTrace_2694206 : CollatzResearch.WordTrace tailWord_2694206 prefixEnd_2694206 307427257828309142296573 := by
  unfold tailWord_2694206
  simp only [CollatzResearch.WordTrace]
  refine ⟨12283220709669908824598809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65510510451572847064526981 12283220709669908824598809)
  ·
    refine ⟨9212415532252431618449107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12283220709669908824598809 9212415532252431618449107)
    ·
      refine ⟨13818623298378647427673661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9212415532252431618449107 13818623298378647427673661)
      ·
        refine ⟨5181983736891992785377623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13818623298378647427673661 5181983736891992785377623)
        ·
          refine ⟨7772975605337989178066435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5181983736891992785377623 7772975605337989178066435)
          ·
            refine ⟨11659463408006983767099653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7772975605337989178066435 11659463408006983767099653)
            ·
              refine ⟨2186149389001309456331185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11659463408006983767099653 2186149389001309456331185)
              ·
                refine ⟨1639612041750982092248389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2186149389001309456331185 1639612041750982092248389)
                ·
                  refine ⟨307427257828309142296573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1639612041750982092248389 307427257828309142296573)
                  ·
                    rfl

theorem cell22_2694206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_2694206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694206 prefixEnd_2694206 := by exact prefixLift 2694206
  have htrace : WordTrace (prefixWord ++ tailWord_2694206) baseStart_2694206 baseEnd_2694206 := by
    simpa [prefixWord, tailWord_2694206, baseEnd_2694206] using wordTrace_append hprefix tailTrace_2694206
  have hstable : (prefixWord ++ tailWord_2694206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694206).length < 2 ^ (prefixWord ++ tailWord_2694206).sum := by decide
  have hdescent : baseEnd_2694206 < baseStart_2694206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694232 : List Nat := [2, 1, 2, 2, 1, 3, 3, 2, 3, 3]
def baseStart_2694232 : Nat := 118140960795 + 2694232 * 2 ^ 59
def prefixEnd_2694232 : Nat := 4983230072969 + 3 ^ 40 * 2694232 * 2
def baseEnd_2694232 : Nat := 922290673816272025739639

theorem tailTrace_2694232 : CollatzResearch.WordTrace tailWord_2694232 prefixEnd_2694232 922290673816272025739639 := by
  unfold tailWord_2694232
  simp only [CollatzResearch.WordTrace]
  refine ⟨49133356987632538518618475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65511142650176718024824633 49133356987632538518618475)
  ·
    refine ⟨73700035481448807777927713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49133356987632538518618475 73700035481448807777927713)
    ·
      refine ⟨55275026611086605833445785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73700035481448807777927713 55275026611086605833445785)
      ·
        refine ⟨41456269958314954375084339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55275026611086605833445785 41456269958314954375084339)
        ·
          refine ⟨62184404937472431562626509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41456269958314954375084339 62184404937472431562626509)
          ·
            refine ⟨23319151851552161835984941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62184404937472431562626509 23319151851552161835984941)
            ·
              refine ⟨8744681944332060688494353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23319151851552161835984941 8744681944332060688494353)
              ·
                refine ⟨6558511458249045516370765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8744681944332060688494353 6558511458249045516370765)
                ·
                  refine ⟨2459441796843392068639037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6558511458249045516370765 2459441796843392068639037)
                  ·
                    refine ⟨922290673816272025739639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2459441796843392068639037 922290673816272025739639)
                    ·
                      rfl

theorem cell22_2694232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_2694232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694232 prefixEnd_2694232 := by exact prefixLift 2694232
  have htrace : WordTrace (prefixWord ++ tailWord_2694232) baseStart_2694232 baseEnd_2694232 := by
    simpa [prefixWord, tailWord_2694232, baseEnd_2694232] using wordTrace_append hprefix tailTrace_2694232
  have hstable : (prefixWord ++ tailWord_2694232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694232).length < 2 ^ (prefixWord ++ tailWord_2694232).sum := by decide
  have hdescent : baseEnd_2694232 < baseStart_2694232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694245 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 7]
def baseStart_2694245 : Nat := 118140960795 + 2694245 * 2 ^ 59
def prefixEnd_2694245 : Nat := 4983230072969 + 3 ^ 40 * 2694245 * 2
def baseEnd_2694245 : Nat := 307431707993981441721533

theorem tailTrace_2694245 : CollatzResearch.WordTrace tailWord_2694245 prefixEnd_2694245 307431707993981441721533 := by
  unfold tailWord_2694245
  simp only [CollatzResearch.WordTrace]
  refine ⟨98267188124217980257460189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65511458749478653504973459 98267188124217980257460189)
  ·
    refine ⟨36850195546581742596547571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98267188124217980257460189 36850195546581742596547571)
    ·
      refine ⟨55275293319872613894821357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36850195546581742596547571 55275293319872613894821357)
      ·
        refine ⟨20728234994952230210558009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55275293319872613894821357 20728234994952230210558009)
        ·
          refine ⟨15546176246214172657918507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20728234994952230210558009 15546176246214172657918507)
          ·
            refine ⟨23319264369321258986877761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15546176246214172657918507 23319264369321258986877761)
            ·
              refine ⟨17489448276990944240158321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23319264369321258986877761 17489448276990944240158321)
              ·
                refine ⟨13117086207743208180118741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17489448276990944240158321 13117086207743208180118741)
                ·
                  refine ⟨307431707993981441721533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13117086207743208180118741 307431707993981441721533)
                  ·
                    rfl

theorem cell22_2694245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_2694245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694245 prefixEnd_2694245 := by exact prefixLift 2694245
  have htrace : WordTrace (prefixWord ++ tailWord_2694245) baseStart_2694245 baseEnd_2694245 := by
    simpa [prefixWord, tailWord_2694245, baseEnd_2694245] using wordTrace_append hprefix tailTrace_2694245
  have hstable : (prefixWord ++ tailWord_2694245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694245).length < 2 ^ (prefixWord ++ tailWord_2694245).sum := by decide
  have hdescent : baseEnd_2694245 < baseStart_2694245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694249 : List Nat := [1, 2, 1, 1, 1, 6, 1, 5, 1, 3]
def baseStart_2694249 : Nat := 118140960795 + 2694249 * 2 ^ 59
def prefixEnd_2694249 : Nat := 4983230072969 + 3 ^ 40 * 2694249 * 2
def baseEnd_2694249 : Nat := 922296493263689648064587

theorem tailTrace_2694249 : CollatzResearch.WordTrace tailWord_2694249 prefixEnd_2694249 922296493263689648064587 := by
  unfold tailWord_2694249
  simp only [CollatzResearch.WordTrace]
  refine ⟨98267334016203488940605801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65511556010802325960403867 98267334016203488940605801)
  ·
    refine ⟨73700500512152616705454351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98267334016203488940605801 73700500512152616705454351)
    ·
      refine ⟨110550750768228925058181527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73700500512152616705454351 110550750768228925058181527)
      ·
        refine ⟨165826126152343387587272291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110550750768228925058181527 165826126152343387587272291)
        ·
          refine ⟨248739189228515081380908437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165826126152343387587272291 248739189228515081380908437)
          ·
            refine ⟨11659649495086644439730083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 248739189228515081380908437 11659649495086644439730083)
            ·
              refine ⟨17489474242629966659595125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11659649495086644439730083 17489474242629966659595125)
              ·
                refine ⟨1639638210246559374337043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17489474242629966659595125 1639638210246559374337043)
                ·
                  refine ⟨2459457315369839061505565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1639638210246559374337043 2459457315369839061505565)
                  ·
                    refine ⟨922296493263689648064587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2459457315369839061505565 922296493263689648064587)
                    ·
                      rfl

theorem cell22_2694249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 1, 3].length) (baseStart_2694249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694249 prefixEnd_2694249 := by exact prefixLift 2694249
  have htrace : WordTrace (prefixWord ++ tailWord_2694249) baseStart_2694249 baseEnd_2694249 := by
    simpa [prefixWord, tailWord_2694249, baseEnd_2694249] using wordTrace_append hprefix tailTrace_2694249
  have hstable : (prefixWord ++ tailWord_2694249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694249).length < 2 ^ (prefixWord ++ tailWord_2694249).sum := by decide
  have hdescent : baseEnd_2694249 < baseStart_2694249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694262 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_2694262 : Nat := 118140960795 + 2694262 * 2 ^ 59
def prefixEnd_2694262 : Nat := 4983230072969 + 3 ^ 40 * 2694262 * 2
def baseEnd_2694262 : Nat := 307433647809787315829849

theorem tailTrace_2694262 : CollatzResearch.WordTrace tailWord_2694262 prefixEnd_2694262 307433647809787315829849 := by
  unfold tailWord_2694262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6141738010322274510051815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65511872110104261440552693 6141738010322274510051815)
  ·
    refine ⟨9212607015483411765077723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6141738010322274510051815 9212607015483411765077723)
    ·
      refine ⟨13818910523225117647616585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9212607015483411765077723 13818910523225117647616585)
      ·
        refine ⟨10364182892418838235712439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13818910523225117647616585 10364182892418838235712439)
        ·
          refine ⟨15546274338628257353568659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10364182892418838235712439 15546274338628257353568659)
          ·
            refine ⟨23319411507942386030352989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15546274338628257353568659 23319411507942386030352989)
            ·
              refine ⟨8744779315478394761382371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23319411507942386030352989 8744779315478394761382371)
              ·
                refine ⟨13117168973217592142073557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8744779315478394761382371 13117168973217592142073557)
                ·
                  refine ⟨307433647809787315829849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13117168973217592142073557 307433647809787315829849)
                  ·
                    rfl

theorem cell22_2694262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_2694262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694262 prefixEnd_2694262 := by exact prefixLift 2694262
  have htrace : WordTrace (prefixWord ++ tailWord_2694262) baseStart_2694262 baseEnd_2694262 := by
    simpa [prefixWord, tailWord_2694262, baseEnd_2694262] using wordTrace_append hprefix tailTrace_2694262
  have hstable : (prefixWord ++ tailWord_2694262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694262).length < 2 ^ (prefixWord ++ tailWord_2694262).sum := by decide
  have hdescent : baseEnd_2694262 < baseStart_2694262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694335 : List Nat := [1, 1, 2, 2, 2, 2, 3, 9]
def baseStart_2694335 : Nat := 118140960795 + 2694335 * 2 ^ 59
def prefixEnd_2694335 : Nat := 4983230072969 + 3 ^ 40 * 2694335 * 2
def baseEnd_2694335 : Nat := 102480659202357121157147

theorem tailTrace_2694335 : CollatzResearch.WordTrace tailWord_2694335 prefixEnd_2694335 102480659202357121157147 := by
  unfold tailWord_2694335
  simp only [CollatzResearch.WordTrace]
  refine ⟨98270470693891925628236459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65513647129261283752157639 98270470693891925628236459)
  ·
    refine ⟨147405706040837888442354689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98270470693891925628236459 147405706040837888442354689)
    ·
      refine ⟨110554279530628416331766017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147405706040837888442354689 110554279530628416331766017)
      ·
        refine ⟨82915709647971312248824513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110554279530628416331766017 82915709647971312248824513)
        ·
          refine ⟨62186782235978484186618385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82915709647971312248824513 62186782235978484186618385)
          ·
            refine ⟨46640086676983863139963789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62186782235978484186618385 46640086676983863139963789)
            ·
              refine ⟨17490032503868948677486421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46640086676983863139963789 17490032503868948677486421)
              ·
                refine ⟨102480659202357121157147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17490032503868948677486421 102480659202357121157147)
                ·
                  rfl

theorem cell22_2694335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 9].length) (baseStart_2694335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694335 prefixEnd_2694335 := by exact prefixLift 2694335
  have htrace : WordTrace (prefixWord ++ tailWord_2694335) baseStart_2694335 baseEnd_2694335 := by
    simpa [prefixWord, tailWord_2694335, baseEnd_2694335] using wordTrace_append hprefix tailTrace_2694335
  have hstable : (prefixWord ++ tailWord_2694335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694335).length < 2 ^ (prefixWord ++ tailWord_2694335).sum := by decide
  have hdescent : baseEnd_2694335 < baseStart_2694335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694354 : List Nat := [3, 2, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_2694354 : Nat := 118140960795 + 2694354 * 2 ^ 59
def prefixEnd_2694354 : Nat := 4983230072969 + 3 ^ 40 * 2694354 * 2
def baseEnd_2694354 : Nat := 922332436909504374189265

theorem tailTrace_2694354 : CollatzResearch.WordTrace tailWord_2694354 prefixEnd_2694354 922332436909504374189265 := by
  unfold tailWord_2694354
  simp only [CollatzResearch.WordTrace]
  refine ⟨24567790920205772968294529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65514109120548727915452077 24567790920205772968294529)
  ·
    refine ⟨18425843190154329726220897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24567790920205772968294529 18425843190154329726220897)
    ·
      refine ⟨13819382392615747294665673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18425843190154329726220897 13819382392615747294665673)
      ·
        refine ⟨10364536794461810470999255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13819382392615747294665673 10364536794461810470999255)
        ·
          refine ⟨15546805191692715706498883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10364536794461810470999255 15546805191692715706498883)
          ·
            refine ⟨23320207787539073559748325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15546805191692715706498883 23320207787539073559748325)
            ·
              refine ⟨4372538960163576292452811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23320207787539073559748325 4372538960163576292452811)
              ·
                refine ⟨6558808440245364438679217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4372538960163576292452811 6558808440245364438679217)
                ·
                  refine ⟨4919106330184023329009413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6558808440245364438679217 4919106330184023329009413)
                  ·
                    refine ⟨922332436909504374189265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4919106330184023329009413 922332436909504374189265)
                    ·
                      rfl

theorem cell22_2694354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_2694354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694354 prefixEnd_2694354 := by exact prefixLift 2694354
  have htrace : WordTrace (prefixWord ++ tailWord_2694354) baseStart_2694354 baseEnd_2694354 := by
    simpa [prefixWord, tailWord_2694354, baseEnd_2694354] using wordTrace_append hprefix tailTrace_2694354
  have hstable : (prefixWord ++ tailWord_2694354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694354).length < 2 ^ (prefixWord ++ tailWord_2694354).sum := by decide
  have hdescent : baseEnd_2694354 < baseStart_2694354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694356 : List Nat := [2, 4, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_2694356 : Nat := 118140960795 + 2694356 * 2 ^ 59
def prefixEnd_2694356 : Nat := 4983230072969 + 3 ^ 40 * 2694356 * 2
def baseEnd_2694356 : Nat := 922333121550377035639259

theorem tailTrace_2694356 : CollatzResearch.WordTrace tailWord_2694356 prefixEnd_2694356 922333121550377035639259 := by
  unfold tailWord_2694356
  simp only [CollatzResearch.WordTrace]
  refine ⟨49135618313407923107375461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65514157751210564143167281 49135618313407923107375461)
  ·
    refine ⟨9212928433763985582632899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49135618313407923107375461 9212928433763985582632899)
    ·
      refine ⟨13819392650645978373949349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9212928433763985582632899 13819392650645978373949349)
      ·
        refine ⟨2591136121996120945115503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13819392650645978373949349 2591136121996120945115503)
        ·
          refine ⟨3886704182994181417673255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2591136121996120945115503 3886704182994181417673255)
          ·
            refine ⟨5830056274491272126509883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3886704182994181417673255 5830056274491272126509883)
            ·
              refine ⟨8745084411736908189764825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5830056274491272126509883 8745084411736908189764825)
              ·
                refine ⟨6558813308802681142323619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8745084411736908189764825 6558813308802681142323619)
                ·
                  refine ⟨9838219963204021713485429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6558813308802681142323619 9838219963204021713485429)
                  ·
                    refine ⟨922333121550377035639259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9838219963204021713485429 922333121550377035639259)
                    ·
                      rfl

theorem cell22_2694356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_2694356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694356 prefixEnd_2694356 := by exact prefixLift 2694356
  have htrace : WordTrace (prefixWord ++ tailWord_2694356) baseStart_2694356 baseEnd_2694356 := by
    simpa [prefixWord, tailWord_2694356, baseEnd_2694356] using wordTrace_append hprefix tailTrace_2694356
  have hstable : (prefixWord ++ tailWord_2694356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694356).length < 2 ^ (prefixWord ++ tailWord_2694356).sum := by decide
  have hdescent : baseEnd_2694356 < baseStart_2694356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694375 : List Nat := [1, 1, 5, 3, 3, 1, 2, 2, 4]
def baseStart_2694375 : Nat := 118140960795 + 2694375 * 2 ^ 59
def prefixEnd_2694375 : Nat := 4983230072969 + 3 ^ 40 * 2694375 * 2
def baseEnd_2694375 : Nat := 307446541879555773138067

theorem tailTrace_2694375 : CollatzResearch.WordTrace tailWord_2694375 prefixEnd_2694375 307446541879555773138067 := by
  unfold tailWord_2694375
  simp only [CollatzResearch.WordTrace]
  refine ⟨98271929613747012459692579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65514619742498008306461719 98271929613747012459692579)
  ·
    refine ⟨147407894420620518689538869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98271929613747012459692579 147407894420620518689538869)
    ·
      refine ⟨13819490101933173627144269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147407894420620518689538869 13819490101933173627144269)
      ·
        refine ⟨5182308788224940110179101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13819490101933173627144269 5182308788224940110179101)
        ·
          refine ⟨1943365795584352541317163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5182308788224940110179101 1943365795584352541317163)
          ·
            refine ⟨2915048693376528811975745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1943365795584352541317163 2915048693376528811975745)
            ·
              refine ⟨2186286520032396608981809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2915048693376528811975745 2186286520032396608981809)
              ·
                refine ⟨1639714890024297456736357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2186286520032396608981809 1639714890024297456736357)
                ·
                  refine ⟨307446541879555773138067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1639714890024297456736357 307446541879555773138067)
                  ·
                    rfl

theorem cell22_2694375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 4].length) (baseStart_2694375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694375 prefixEnd_2694375 := by exact prefixLift 2694375
  have htrace : WordTrace (prefixWord ++ tailWord_2694375) baseStart_2694375 baseEnd_2694375 := by
    simpa [prefixWord, tailWord_2694375, baseEnd_2694375] using wordTrace_append hprefix tailTrace_2694375
  have hstable : (prefixWord ++ tailWord_2694375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694375).length < 2 ^ (prefixWord ++ tailWord_2694375).sum := by decide
  have hdescent : baseEnd_2694375 < baseStart_2694375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694382 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_2694382 : Nat := 118140960795 + 2694382 * 2 ^ 59
def prefixEnd_2694382 : Nat := 4983230072969 + 3 ^ 40 * 2694382 * 2
def baseEnd_2694382 : Nat := 922342021881721634489179

theorem tailTrace_2694382 : CollatzResearch.WordTrace tailWord_2694382 prefixEnd_2694382 922342021881721634489179 := by
  unfold tailWord_2694382
  simp only [CollatzResearch.WordTrace]
  refine ⟨12284023115590206581899675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65514789949814435103464933 12284023115590206581899675)
  ·
    refine ⟨18426034673385309872849513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12284023115590206581899675 18426034673385309872849513)
    ·
      refine ⟨13819526005038982404637135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18426034673385309872849513 13819526005038982404637135)
      ·
        refine ⟨20729289007558473606955703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13819526005038982404637135 20729289007558473606955703)
        ·
          refine ⟨31093933511337710410433555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20729289007558473606955703 31093933511337710410433555)
          ·
            refine ⟨46640900267006565615650333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31093933511337710410433555 46640900267006565615650333)
            ·
              refine ⟨17490337600127462105868875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46640900267006565615650333 17490337600127462105868875)
              ·
                refine ⟨26235506400191193158803313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17490337600127462105868875 26235506400191193158803313)
                ·
                  refine ⟨19676629800143394869102485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26235506400191193158803313 19676629800143394869102485)
                  ·
                    refine ⟨922342021881721634489179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19676629800143394869102485 922342021881721634489179)
                    ·
                      rfl

theorem cell22_2694382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_2694382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694382 prefixEnd_2694382 := by exact prefixLift 2694382
  have htrace : WordTrace (prefixWord ++ tailWord_2694382) baseStart_2694382 baseEnd_2694382 := by
    simpa [prefixWord, tailWord_2694382, baseEnd_2694382] using wordTrace_append hprefix tailTrace_2694382
  have hstable : (prefixWord ++ tailWord_2694382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694382).length < 2 ^ (prefixWord ++ tailWord_2694382).sum := by decide
  have hdescent : baseEnd_2694382 < baseStart_2694382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694386 : List Nat := [3, 2, 1, 3, 4, 1, 1, 7]
def baseStart_2694386 : Nat := 118140960795 + 2694386 * 2 ^ 59
def prefixEnd_2694386 : Nat := 4983230072969 + 3 ^ 40 * 2694386 * 2
def baseEnd_2694386 : Nat := 102482599018162995265463

theorem tailTrace_2694386 : CollatzResearch.WordTrace tailWord_2694386 prefixEnd_2694386 102482599018162995265463 := by
  unfold tailWord_2694386
  simp only [CollatzResearch.WordTrace]
  refine ⟨24568082704176790334585753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65514887211138107558895341 24568082704176790334585753)
  ·
    refine ⟨18426062028132592750939315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24568082704176790334585753 18426062028132592750939315)
    ·
      refine ⟨27639093042198889126408973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18426062028132592750939315 27639093042198889126408973)
      ·
        refine ⟨10364659890824583422403365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27639093042198889126408973 10364659890824583422403365)
        ·
          refine ⟨1943373729529609391700631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10364659890824583422403365 1943373729529609391700631)
          ·
            refine ⟨2915060594294414087550947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1943373729529609391700631 2915060594294414087550947)
            ·
              refine ⟨4372590891441621131326421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2915060594294414087550947 4372590891441621131326421)
              ·
                refine ⟨102482599018162995265463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4372590891441621131326421 102482599018162995265463)
                ·
                  rfl

theorem cell22_2694386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 7].length) (baseStart_2694386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694386 prefixEnd_2694386 := by exact prefixLift 2694386
  have htrace : WordTrace (prefixWord ++ tailWord_2694386) baseStart_2694386 baseEnd_2694386 := by
    simpa [prefixWord, tailWord_2694386, baseEnd_2694386] using wordTrace_append hprefix tailTrace_2694386
  have hstable : (prefixWord ++ tailWord_2694386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694386).length < 2 ^ (prefixWord ++ tailWord_2694386).sum := by decide
  have hdescent : baseEnd_2694386 < baseStart_2694386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694429 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_2694429 : Nat := 118140960795 + 2694429 * 2 ^ 59
def prefixEnd_2694429 : Nat := 4983230072969 + 3 ^ 40 * 2694429 * 2
def baseEnd_2694429 : Nat := 922358110942229178564035

theorem tailTrace_2694429 : CollatzResearch.WordTrace tailWord_2694429 prefixEnd_2694429 922358110942229178564035 := by
  unfold tailWord_2694429
  simp only [CollatzResearch.WordTrace]
  refine ⟨98273899155551379682158341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65515932770367586454772227 98273899155551379682158341)
  ·
    refine ⟨18426356091665883690404689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98273899155551379682158341 18426356091665883690404689)
    ·
      refine ⟨13819767068749412767803517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18426356091665883690404689 13819767068749412767803517)
      ·
        refine ⟨5182412650781029787926319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13819767068749412767803517 5182412650781029787926319)
        ·
          refine ⟨7773618976171544681889479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5182412650781029787926319 7773618976171544681889479)
          ·
            refine ⟨11660428464257317022834219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7773618976171544681889479 11660428464257317022834219)
            ·
              refine ⟨17490642696385975534251329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11660428464257317022834219 17490642696385975534251329)
              ·
                refine ⟨13117982022289481650688497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17490642696385975534251329 13117982022289481650688497)
                ·
                  refine ⟨9838486516717111238016373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13117982022289481650688497 9838486516717111238016373)
                  ·
                    refine ⟨922358110942229178564035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9838486516717111238016373 922358110942229178564035)
                    ·
                      rfl

theorem cell22_2694429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_2694429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694429 prefixEnd_2694429 := by exact prefixLift 2694429
  have htrace : WordTrace (prefixWord ++ tailWord_2694429) baseStart_2694429 baseEnd_2694429 := by
    simpa [prefixWord, tailWord_2694429, baseEnd_2694429] using wordTrace_append hprefix tailTrace_2694429
  have hstable : (prefixWord ++ tailWord_2694429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694429).length < 2 ^ (prefixWord ++ tailWord_2694429).sum := by decide
  have hdescent : baseEnd_2694429 < baseStart_2694429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694431 : List Nat := [1, 1, 2, 4, 4, 2, 1, 2, 5]
def baseStart_2694431 : Nat := 118140960795 + 2694431 * 2 ^ 59
def prefixEnd_2694431 : Nat := 4983230072969 + 3 ^ 40 * 2694431 * 2
def baseEnd_2694431 : Nat := 307452931861033946671343

theorem tailTrace_2694431 : CollatzResearch.WordTrace tailWord_2694431 prefixEnd_2694431 307452931861033946671343 := by
  unfold tailWord_2694431
  simp only [CollatzResearch.WordTrace]
  refine ⟨98273972101544134023731147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65515981401029422682487431 98273972101544134023731147)
  ·
    refine ⟨147410958152316201035596721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98273972101544134023731147 147410958152316201035596721)
    ·
      refine ⟨110558218614237150776697541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147410958152316201035596721 110558218614237150776697541)
      ·
        refine ⟨20729665990169465770630789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110558218614237150776697541 20729665990169465770630789)
        ·
          refine ⟨3886812373156774831993273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20729665990169465770630789 3886812373156774831993273)
          ·
            refine ⟨2915109279867581123994955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3886812373156774831993273 2915109279867581123994955)
            ·
              refine ⟨4372663919801371685992433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2915109279867581123994955 4372663919801371685992433)
              ·
                refine ⟨3279497939851028764494325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4372663919801371685992433 3279497939851028764494325)
                ·
                  refine ⟨307452931861033946671343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3279497939851028764494325 307452931861033946671343)
                  ·
                    rfl

theorem cell22_2694431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 5].length) (baseStart_2694431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694431 prefixEnd_2694431 := by exact prefixLift 2694431
  have htrace : WordTrace (prefixWord ++ tailWord_2694431) baseStart_2694431 baseEnd_2694431 := by
    simpa [prefixWord, tailWord_2694431, baseEnd_2694431] using wordTrace_append hprefix tailTrace_2694431
  have hstable : (prefixWord ++ tailWord_2694431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694431).length < 2 ^ (prefixWord ++ tailWord_2694431).sum := by decide
  have hdescent : baseEnd_2694431 < baseStart_2694431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694476 : List Nat := [2, 2, 1, 3, 2, 2, 3, 3, 4]
def baseStart_2694476 : Nat := 118140960795 + 2694476 * 2 ^ 59
def prefixEnd_2694476 : Nat := 4983230072969 + 3 ^ 40 * 2694476 * 2
def baseEnd_2694476 : Nat := 307458066667578907546297

theorem tailTrace_2694476 : CollatzResearch.WordTrace tailWord_2694476 prefixEnd_2694476 307458066667578907546297 := by
  unfold tailWord_2694476
  simp only [CollatzResearch.WordTrace]
  refine ⟨49137806693190553354559641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65517075590920737806079521 49137806693190553354559641)
  ·
    refine ⟨36853355019892915015919731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49137806693190553354559641 36853355019892915015919731)
    ·
      refine ⟨55280032529839372523879597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36853355019892915015919731 55280032529839372523879597)
      ·
        refine ⟨20730012198689764696454849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55280032529839372523879597 20730012198689764696454849)
        ·
          refine ⟨15547509149017323522341137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20730012198689764696454849 15547509149017323522341137)
          ·
            refine ⟨11660631861762992641755853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15547509149017323522341137 11660631861762992641755853)
            ·
              refine ⟨4372736948161122240658445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11660631861762992641755853 4372736948161122240658445)
              ·
                refine ⟨1639776355560420840246917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4372736948161122240658445 1639776355560420840246917)
                ·
                  refine ⟨307458066667578907546297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1639776355560420840246917 307458066667578907546297)
                  ·
                    rfl

theorem cell22_2694476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_2694476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694476 prefixEnd_2694476 := by exact prefixLift 2694476
  have htrace : WordTrace (prefixWord ++ tailWord_2694476) baseStart_2694476 baseEnd_2694476 := by
    simpa [prefixWord, tailWord_2694476, baseEnd_2694476] using wordTrace_append hprefix tailTrace_2694476
  have hstable : (prefixWord ++ tailWord_2694476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694476).length < 2 ^ (prefixWord ++ tailWord_2694476).sum := by decide
  have hdescent : baseEnd_2694476 < baseStart_2694476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694486 : List Nat := [5, 2, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_2694486 : Nat := 118140960795 + 2694486 * 2 ^ 59
def prefixEnd_2694486 : Nat := 4983230072969 + 3 ^ 40 * 2694486 * 2
def baseEnd_2694486 : Nat := 922377623207100029888861

theorem tailTrace_2694486 : CollatzResearch.WordTrace tailWord_2694486 prefixEnd_2694486 922377623207100029888861 := by
  unfold tailWord_2694486
  simp only [CollatzResearch.WordTrace]
  refine ⟨6142248632271554901061457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65517318744229918944655541 6142248632271554901061457)
  ·
    refine ⟨4606686474203666175796093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6142248632271554901061457 4606686474203666175796093)
    ·
      refine ⟨1727507427826374815923535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4606686474203666175796093 1727507427826374815923535)
      ·
        refine ⟨2591261141739562223885303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1727507427826374815923535 2591261141739562223885303)
        ·
          refine ⟨3886891712609343335827955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2591261141739562223885303 3886891712609343335827955)
          ·
            refine ⟨5830337568914015003741933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3886891712609343335827955 5830337568914015003741933)
            ·
              refine ⟨2186376588342755626403225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5830337568914015003741933 2186376588342755626403225)
              ·
                refine ⟨1639782441257066719802419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2186376588342755626403225 1639782441257066719802419)
                ·
                  refine ⟨2459673661885600079703629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1639782441257066719802419 2459673661885600079703629)
                  ·
                    refine ⟨922377623207100029888861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2459673661885600079703629 922377623207100029888861)
                    ·
                      rfl

theorem cell22_2694486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_2694486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694486 prefixEnd_2694486 := by exact prefixLift 2694486
  have htrace : WordTrace (prefixWord ++ tailWord_2694486) baseStart_2694486 baseEnd_2694486 := by
    simpa [prefixWord, tailWord_2694486, baseEnd_2694486] using wordTrace_append hprefix tailTrace_2694486
  have hstable : (prefixWord ++ tailWord_2694486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694486).length < 2 ^ (prefixWord ++ tailWord_2694486).sum := by decide
  have hdescent : baseEnd_2694486 < baseStart_2694486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694487 : List Nat := [1, 1, 3, 2, 3, 2, 10]
def baseStart_2694487 : Nat := 118140960795 + 2694487 * 2 ^ 59
def prefixEnd_2694487 : Nat := 4983230072969 + 3 ^ 40 * 2694487 * 2
def baseEnd_2694487 : Nat := 34162146871390235578291

theorem tailTrace_2694487 : CollatzResearch.WordTrace tailWord_2694487 prefixEnd_2694487 34162146871390235578291 := by
  unfold tailWord_2694487
  simp only [CollatzResearch.WordTrace]
  refine ⟨98276014589341255587769715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65517343059560837058513143 98276014589341255587769715)
  ·
    refine ⟨147414021884011883381654573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98276014589341255587769715 147414021884011883381654573)
    ·
      refine ⟨55280258206504456268120465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147414021884011883381654573 55280258206504456268120465)
      ·
        refine ⟨41460193654878342201090349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55280258206504456268120465 41460193654878342201090349)
        ·
          refine ⟨15547572620579378325408881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41460193654878342201090349 15547572620579378325408881)
          ·
            refine ⟨11660679465434533744056661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15547572620579378325408881 11660679465434533744056661)
            ·
              refine ⟨34162146871390235578291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11660679465434533744056661 34162146871390235578291)
              ·
                rfl

theorem cell22_2694487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 10].length) (baseStart_2694487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694487 prefixEnd_2694487 := by exact prefixLift 2694487
  have htrace : WordTrace (prefixWord ++ tailWord_2694487) baseStart_2694487 baseEnd_2694487 := by
    simpa [prefixWord, tailWord_2694487, baseEnd_2694487] using wordTrace_append hprefix tailTrace_2694487
  have hstable : (prefixWord ++ tailWord_2694487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694487).length < 2 ^ (prefixWord ++ tailWord_2694487).sum := by decide
  have hdescent : baseEnd_2694487 < baseStart_2694487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694508 : List Nat := [2, 2, 1, 1, 5, 1, 4, 1, 2, 3]
def baseStart_2694508 : Nat := 118140960795 + 2694508 * 2 ^ 59
def prefixEnd_2694508 : Nat := 4983230072969 + 3 ^ 40 * 2694508 * 2
def baseEnd_2694508 : Nat := 922385154256699305838793

theorem tailTrace_2694508 : CollatzResearch.WordTrace tailWord_2694508 prefixEnd_2694508 922385154256699305838793 := by
  unfold tailWord_2694508
  simp only [CollatzResearch.WordTrace]
  refine ⟨49138390261132588087142089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65517853681510117449522785 49138390261132588087142089)
  ·
    refine ⟨36853792695849441065356567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49138390261132588087142089 36853792695849441065356567)
    ·
      refine ⟨55280689043774161598034851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36853792695849441065356567 55280689043774161598034851)
      ·
        refine ⟨82921033565661242397052277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55280689043774161598034851 82921033565661242397052277)
        ·
          refine ⟨7773846896780741474723651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82921033565661242397052277 7773846896780741474723651)
          ·
            refine ⟨11660770345171112212085477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7773846896780741474723651 11660770345171112212085477)
            ·
              refine ⟨2186394439719583539766027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11660770345171112212085477 2186394439719583539766027)
              ·
                refine ⟨3279591659579375309649041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2186394439719583539766027 3279591659579375309649041)
                ·
                  refine ⟨2459693744684531482236781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3279591659579375309649041 2459693744684531482236781)
                  ·
                    refine ⟨922385154256699305838793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2459693744684531482236781 922385154256699305838793)
                    ·
                      rfl

theorem cell22_2694508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 3].length) (baseStart_2694508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694508 prefixEnd_2694508 := by exact prefixLift 2694508
  have htrace : WordTrace (prefixWord ++ tailWord_2694508) baseStart_2694508 baseEnd_2694508 := by
    simpa [prefixWord, tailWord_2694508, baseEnd_2694508] using wordTrace_append hprefix tailTrace_2694508
  have hstable : (prefixWord ++ tailWord_2694508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694508).length < 2 ^ (prefixWord ++ tailWord_2694508).sum := by decide
  have hdescent : baseEnd_2694508 < baseStart_2694508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694519 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 5, 3]
def baseStart_2694519 : Nat := 118140960795 + 2694519 * 2 ^ 59
def prefixEnd_2694519 : Nat := 4983230072969 + 3 ^ 40 * 2694519 * 2
def baseEnd_2694519 : Nat := 922388919781498943813759

theorem tailTrace_2694519 : CollatzResearch.WordTrace tailWord_2694519 prefixEnd_2694519 922388919781498943813759 := by
  unfold tailWord_2694519
  simp only [CollatzResearch.WordTrace]
  refine ⟨98277181725225325052934611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65518121150150216701956407 98277181725225325052934611)
  ·
    refine ⟨147415772587837987579401917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98277181725225325052934611 147415772587837987579401917)
    ·
      refine ⟨55280914720439245342275719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147415772587837987579401917 55280914720439245342275719)
      ·
        refine ⟨82921372080658868013413579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55280914720439245342275719 82921372080658868013413579)
        ·
          refine ⟨124382058120988302020120369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82921372080658868013413579 124382058120988302020120369)
          ·
            refine ⟨93286543590741226515090277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124382058120988302020120369 93286543590741226515090277)
            ·
              refine ⟨17491226923263979971579427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93286543590741226515090277 17491226923263979971579427)
              ·
                refine ⟨26236840384895969957369141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17491226923263979971579427 26236840384895969957369141)
                ·
                  refine ⟨2459703786083997183503357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26236840384895969957369141 2459703786083997183503357)
                  ·
                    refine ⟨922388919781498943813759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2459703786083997183503357 922388919781498943813759)
                    ·
                      rfl

theorem cell22_2694519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_2694519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694519 prefixEnd_2694519 := by exact prefixLift 2694519
  have htrace : WordTrace (prefixWord ++ tailWord_2694519) baseStart_2694519 baseEnd_2694519 := by
    simpa [prefixWord, tailWord_2694519, baseEnd_2694519] using wordTrace_append hprefix tailTrace_2694519
  have hstable : (prefixWord ++ tailWord_2694519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694519).length < 2 ^ (prefixWord ++ tailWord_2694519).sum := by decide
  have hdescent : baseEnd_2694519 < baseStart_2694519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694547 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 5, 7]
def baseStart_2694547 : Nat := 118140960795 + 2694547 * 2 ^ 59
def prefixEnd_2694547 : Nat := 4983230072969 + 3 ^ 40 * 2694547 * 2
def baseEnd_2694547 : Nat := 922398504753716204113673

theorem tailTrace_2694547 : CollatzResearch.WordTrace tailWord_2694547 prefixEnd_2694547 922398504753716204113673 := by
  unfold tailWord_2694547
  simp only [CollatzResearch.WordTrace]
  refine ⟨98278202969123885834953895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65518801979415923889969263 98278202969123885834953895)
  ·
    refine ⟨147417304453685828752430843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98278202969123885834953895 147417304453685828752430843)
    ·
      refine ⟨221125956680528743128646265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147417304453685828752430843 221125956680528743128646265)
      ·
        refine ⟨165844467510396557346484699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221125956680528743128646265 165844467510396557346484699)
        ·
          refine ⟨248766701265594836019727049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165844467510396557346484699 248766701265594836019727049)
          ·
            refine ⟨186575025949196127014795287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248766701265594836019727049 186575025949196127014795287)
            ·
              refine ⟨279862538923794190522192931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186575025949196127014795287 279862538923794190522192931)
              ·
                refine ⟨419793808385691285783289397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279862538923794190522192931 419793808385691285783289397)
                ·
                  refine ⟨39355669536158558042183381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 419793808385691285783289397 39355669536158558042183381)
                  ·
                    refine ⟨922398504753716204113673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39355669536158558042183381 922398504753716204113673)
                    ·
                      rfl

theorem cell22_2694547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 7].length) (baseStart_2694547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694547 prefixEnd_2694547 := by exact prefixLift 2694547
  have htrace : WordTrace (prefixWord ++ tailWord_2694547) baseStart_2694547 baseEnd_2694547 := by
    simpa [prefixWord, tailWord_2694547, baseEnd_2694547] using wordTrace_append hprefix tailTrace_2694547
  have hstable : (prefixWord ++ tailWord_2694547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694547).length < 2 ^ (prefixWord ++ tailWord_2694547).sum := by decide
  have hdescent : baseEnd_2694547 < baseStart_2694547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694549 : List Nat := [1, 3, 2, 1, 1, 2, 3, 4, 5]
def baseStart_2694549 : Nat := 118140960795 + 2694549 * 2 ^ 59
def prefixEnd_2694549 : Nat := 4983230072969 + 3 ^ 40 * 2694549 * 2
def baseEnd_2694549 : Nat := 307466396464862955187889

theorem tailTrace_2694549 : CollatzResearch.WordTrace tailWord_2694549 prefixEnd_2694549 307466396464862955187889 := by
  unfold tailWord_2694549
  simp only [CollatzResearch.WordTrace]
  refine ⟨98278275915116640176526701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65518850610077760117684467 98278275915116640176526701)
  ·
    refine ⟨36854353468168740066197513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98278275915116640176526701 36854353468168740066197513)
    ·
      refine ⟨27640765101126555049648135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36854353468168740066197513 27640765101126555049648135)
      ·
        refine ⟨41461147651689832574472203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27640765101126555049648135 41461147651689832574472203)
        ·
          refine ⟨62191721477534748861708305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41461147651689832574472203 62191721477534748861708305)
          ·
            refine ⟨46643791108151061646281229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62191721477534748861708305 46643791108151061646281229)
            ·
              refine ⟨17491421665556648117355461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46643791108151061646281229 17491421665556648117355461)
              ·
                refine ⟨3279641562291871522004149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17491421665556648117355461 3279641562291871522004149)
                ·
                  refine ⟨307466396464862955187889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3279641562291871522004149 307466396464862955187889)
                  ·
                    rfl

theorem cell22_2694549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_2694549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694549 prefixEnd_2694549 := by exact prefixLift 2694549
  have htrace : WordTrace (prefixWord ++ tailWord_2694549) baseStart_2694549 baseEnd_2694549 := by
    simpa [prefixWord, tailWord_2694549, baseEnd_2694549] using wordTrace_append hprefix tailTrace_2694549
  have hstable : (prefixWord ++ tailWord_2694549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694549).length < 2 ^ (prefixWord ++ tailWord_2694549).sum := by decide
  have hdescent : baseEnd_2694549 < baseStart_2694549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694553 : List Nat := [1, 2, 1, 2, 1, 6, 1, 4, 1, 3]
def baseStart_2694553 : Nat := 118140960795 + 2694553 * 2 ^ 59
def prefixEnd_2694553 : Nat := 4983230072969 + 3 ^ 40 * 2694553 * 2
def baseEnd_2694553 : Nat := 922400558676334188463655

theorem tailTrace_2694553 : CollatzResearch.WordTrace tailWord_2694553 prefixEnd_2694553 922400558676334188463655 := by
  unfold tailWord_2694553
  simp only [CollatzResearch.WordTrace]
  refine ⟨98278421807102148859672313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65518947871401432573114875 98278421807102148859672313)
  ·
    refine ⟨73708816355326611644754235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98278421807102148859672313 73708816355326611644754235)
    ·
      refine ⟨110563224532989917467131353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73708816355326611644754235 110563224532989917467131353)
      ·
        refine ⟨82922418399742438100348515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110563224532989917467131353 82922418399742438100348515)
        ·
          refine ⟨124383627599613657150522773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82922418399742438100348515 124383627599613657150522773)
          ·
            refine ⟨5830482543731890178930755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124383627599613657150522773 5830482543731890178930755)
            ·
              refine ⟨8745723815597835268396133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5830482543731890178930755 8745723815597835268396133)
              ·
                refine ⟨1639823215424594112824275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8745723815597835268396133 1639823215424594112824275)
                ·
                  refine ⟨2459734823136891169236413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1639823215424594112824275 2459734823136891169236413)
                  ·
                    refine ⟨922400558676334188463655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2459734823136891169236413 922400558676334188463655)
                    ·
                      rfl

theorem cell22_2694553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 1, 3].length) (baseStart_2694553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694553 prefixEnd_2694553 := by exact prefixLift 2694553
  have htrace : WordTrace (prefixWord ++ tailWord_2694553) baseStart_2694553 baseEnd_2694553 := by
    simpa [prefixWord, tailWord_2694553, baseEnd_2694553] using wordTrace_append hprefix tailTrace_2694553
  have hstable : (prefixWord ++ tailWord_2694553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694553).length < 2 ^ (prefixWord ++ tailWord_2694553).sum := by decide
  have hdescent : baseEnd_2694553 < baseStart_2694553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694624 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 6, 4]
def baseStart_2694624 : Nat := 118140960795 + 2694624 * 2 ^ 59
def prefixEnd_2694624 : Nat := 4983230072969 + 3 ^ 40 * 2694624 * 2
def baseEnd_2694624 : Nat := 922424863427313669938437

theorem tailTrace_2694624 : CollatzResearch.WordTrace tailWord_2694624 prefixEnd_2694624 922424863427313669938437 := by
  unfold tailWord_2694624
  simp only [CollatzResearch.WordTrace]
  refine ⟨49140505694922463992753463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65520674259896618657004617 49140505694922463992753463)
  ·
    refine ⟨73710758542383695989130195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49140505694922463992753463 73710758542383695989130195)
    ·
      refine ⟨110566137813575543983695293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73710758542383695989130195 110566137813575543983695293)
      ·
        refine ⟨41462301680090828993885735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110566137813575543983695293 41462301680090828993885735)
        ·
          refine ⟨62193452520136243490828603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41462301680090828993885735 62193452520136243490828603)
          ·
            refine ⟨93290178780204365236242905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62193452520136243490828603 93290178780204365236242905)
            ·
              refine ⟨69967634085153273927182179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93290178780204365236242905 69967634085153273927182179)
              ·
                refine ⟨104951451127729910890773269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69967634085153273927182179 104951451127729910890773269)
                ·
                  refine ⟨4919599271612339573004997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104951451127729910890773269 4919599271612339573004997)
                  ·
                    refine ⟨922424863427313669938437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4919599271612339573004997 922424863427313669938437)
                    ·
                      rfl

theorem cell22_2694624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_2694624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694624 prefixEnd_2694624 := by exact prefixLift 2694624
  have htrace : WordTrace (prefixWord ++ tailWord_2694624) baseStart_2694624 baseEnd_2694624 := by
    simpa [prefixWord, tailWord_2694624, baseEnd_2694624] using wordTrace_append hprefix tailTrace_2694624
  have hstable : (prefixWord ++ tailWord_2694624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694624).length < 2 ^ (prefixWord ++ tailWord_2694624).sum := by decide
  have hdescent : baseEnd_2694624 < baseStart_2694624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694645 : List Nat := [1, 3, 5, 1, 1, 1, 3, 3, 4]
def baseStart_2694645 : Nat := 118140960795 + 2694645 * 2 ^ 59
def prefixEnd_2694645 : Nat := 4983230072969 + 3 ^ 40 * 2694645 * 2
def baseEnd_2694645 : Nat := 307477350718825538387791

theorem tailTrace_2694645 : CollatzResearch.WordTrace tailWord_2694645 prefixEnd_2694645 307477350718825538387791 := by
  unfold tailWord_2694645
  simp only [CollatzResearch.WordTrace]
  refine ⟨98281777322768848572021389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65521184881845899048014259 98281777322768848572021389)
  ·
    refine ⟨36855666496038318214508021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98281777322768848572021389 36855666496038318214508021)
    ·
      refine ⟨3455218734003592332610127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36855666496038318214508021 3455218734003592332610127)
      ·
        refine ⟨5182828101005388498915191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3455218734003592332610127 5182828101005388498915191)
        ·
          refine ⟨7774242151508082748372787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5182828101005388498915191 7774242151508082748372787)
          ·
            refine ⟨11661363227262124122559181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7774242151508082748372787 11661363227262124122559181)
            ·
              refine ⟨4373011210223296545959693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11661363227262124122559181 4373011210223296545959693)
              ·
                refine ⟨1639879203833736204734885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4373011210223296545959693 1639879203833736204734885)
                ·
                  refine ⟨307477350718825538387791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1639879203833736204734885 307477350718825538387791)
                  ·
                    rfl

theorem cell22_2694645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_2694645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694645 prefixEnd_2694645 := by exact prefixLift 2694645
  have htrace : WordTrace (prefixWord ++ tailWord_2694645) baseStart_2694645 baseEnd_2694645 := by
    simpa [prefixWord, tailWord_2694645, baseEnd_2694645] using wordTrace_append hprefix tailTrace_2694645
  have hstable : (prefixWord ++ tailWord_2694645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694645).length < 2 ^ (prefixWord ++ tailWord_2694645).sum := by decide
  have hdescent : baseEnd_2694645 < baseStart_2694645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694658 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_2694658 : Nat := 118140960795 + 2694658 * 2 ^ 59
def prefixEnd_2694658 : Nat := 4983230072969 + 3 ^ 40 * 2694658 * 2
def baseEnd_2694658 : Nat := 922436502322148914588333

theorem tailTrace_2694658 : CollatzResearch.WordTrace tailWord_2694658 prefixEnd_2694658 922436502322148914588333 := by
  unfold tailWord_2694658
  simp only [CollatzResearch.WordTrace]
  refine ⟨24570562867930437948061157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65521500981147834528163085 24570562867930437948061157)
  ·
    refine ⟨4606980537736957115261467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24570562867930437948061157 4606980537736957115261467)
    ·
      refine ⟨6910470806605435672892201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4606980537736957115261467 6910470806605435672892201)
      ·
        refine ⟨5182853104954076754669151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6910470806605435672892201 5182853104954076754669151)
        ·
          refine ⟨7774279657431115132003727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5182853104954076754669151 7774279657431115132003727)
          ·
            refine ⟨11661419486146672698005591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7774279657431115132003727 11661419486146672698005591)
            ·
              refine ⟨17492129229220009047008387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11661419486146672698005591 17492129229220009047008387)
              ·
                refine ⟨26238193843830013570512581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17492129229220009047008387 26238193843830013570512581)
                ·
                  refine ⟨4919661345718127544471109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26238193843830013570512581 4919661345718127544471109)
                  ·
                    refine ⟨922436502322148914588333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4919661345718127544471109 922436502322148914588333)
                    ·
                      rfl

theorem cell22_2694658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_2694658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694658 prefixEnd_2694658 := by exact prefixLift 2694658
  have htrace : WordTrace (prefixWord ++ tailWord_2694658) baseStart_2694658 baseEnd_2694658 := by
    simpa [prefixWord, tailWord_2694658, baseEnd_2694658] using wordTrace_append hprefix tailTrace_2694658
  have hstable : (prefixWord ++ tailWord_2694658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694658).length < 2 ^ (prefixWord ++ tailWord_2694658).sum := by decide
  have hdescent : baseEnd_2694658 < baseStart_2694658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694699 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 6, 5]
def baseStart_2694699 : Nat := 118140960795 + 2694699 * 2 ^ 59
def prefixEnd_2694699 : Nat := 4983230072969 + 3 ^ 40 * 2694699 * 2
def baseEnd_2694699 : Nat := 922450537460038474313207

theorem tailTrace_2694699 : CollatzResearch.WordTrace tailWord_2694699 prefixEnd_2694699 922450537460038474313207 := by
  unfold tailWord_2694699
  simp only [CollatzResearch.WordTrace]
  refine ⟨98283746864573215794487151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65522497909715477196324767 98283746864573215794487151)
  ·
    refine ⟨147425620296859823691730727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98283746864573215794487151 147425620296859823691730727)
    ·
      refine ⟨221138430445289735537596091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147425620296859823691730727 221138430445289735537596091)
      ·
        refine ⟨331707645667934603306394137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221138430445289735537596091 331707645667934603306394137)
        ·
          refine ⟨248780734250950952479795603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331707645667934603306394137 248780734250950952479795603)
          ·
            refine ⟨373171101376426428719693405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248780734250950952479795603 373171101376426428719693405)
            ·
              refine ⟨139939163016159910769885027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 373171101376426428719693405 139939163016159910769885027)
              ·
                refine ⟨209908744524239866154827541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139939163016159910769885027 209908744524239866154827541)
                ·
                  refine ⟨9839472399573743726007541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 209908744524239866154827541 9839472399573743726007541)
                  ·
                    refine ⟨922450537460038474313207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9839472399573743726007541 922450537460038474313207)
                    ·
                      rfl

theorem cell22_2694699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 5].length) (baseStart_2694699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694699 prefixEnd_2694699 := by exact prefixLift 2694699
  have htrace : WordTrace (prefixWord ++ tailWord_2694699) baseStart_2694699 baseEnd_2694699 := by
    simpa [prefixWord, tailWord_2694699, baseEnd_2694699] using wordTrace_append hprefix tailTrace_2694699
  have hstable : (prefixWord ++ tailWord_2694699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694699).length < 2 ^ (prefixWord ++ tailWord_2694699).sum := by decide
  have hdescent : baseEnd_2694699 < baseStart_2694699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694729 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 10]
def baseStart_2694729 : Nat := 118140960795 + 2694729 * 2 ^ 59
def prefixEnd_2694729 : Nat := 4983230072969 + 3 ^ 40 * 2694729 * 2
def baseEnd_2694729 : Nat := 307486935691042798687705

theorem tailTrace_2694729 : CollatzResearch.WordTrace tailWord_2694729 prefixEnd_2694729 307486935691042798687705 := by
  unfold tailWord_2694729
  simp only [CollatzResearch.WordTrace]
  refine ⟨98284841054464530918079241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65523227369643020612052827 98284841054464530918079241)
  ·
    refine ⟨73713630790848398188559431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98284841054464530918079241 73713630790848398188559431)
    ·
      refine ⟨110570446186272597282839147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73713630790848398188559431 110570446186272597282839147)
      ·
        refine ⟨165855669279408895924258721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110570446186272597282839147 165855669279408895924258721)
        ·
          refine ⟨124391751959556671943194041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165855669279408895924258721 124391751959556671943194041)
          ·
            refine ⟨93293813969667503957395531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124391751959556671943194041 93293813969667503957395531)
            ·
              refine ⟨139940720954501255936093297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93293813969667503957395531 139940720954501255936093297)
              ·
                refine ⟨104955540715875941952069973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139940720954501255936093297 104955540715875941952069973)
                ·
                  refine ⟨307486935691042798687705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 104955540715875941952069973 307486935691042798687705)
                  ·
                    rfl

theorem cell22_2694729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 10].length) (baseStart_2694729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694729 prefixEnd_2694729 := by exact prefixLift 2694729
  have htrace : WordTrace (prefixWord ++ tailWord_2694729) baseStart_2694729 baseEnd_2694729 := by
    simpa [prefixWord, tailWord_2694729, baseEnd_2694729] using wordTrace_append hprefix tailTrace_2694729
  have hstable : (prefixWord ++ tailWord_2694729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694729).length < 2 ^ (prefixWord ++ tailWord_2694729).sum := by decide
  have hdescent : baseEnd_2694729 < baseStart_2694729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694748 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 3, 4]
def baseStart_2694748 : Nat := 118140960795 + 2694748 * 2 ^ 59
def prefixEnd_2694748 : Nat := 4983230072969 + 3 ^ 40 * 2694748 * 2
def baseEnd_2694748 : Nat := 922467311161418679838057

theorem tailTrace_2694748 : CollatzResearch.WordTrace tailWord_2694748 prefixEnd_2694748 922467311161418679838057 := by
  unfold tailWord_2694748
  simp only [CollatzResearch.WordTrace]
  refine ⟨49142767020697848581510449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65523689360930464775347265 49142767020697848581510449)
  ·
    refine ⟨36857075265523386436132837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49142767020697848581510449 36857075265523386436132837)
    ·
      refine ⟨6910701612285634956774907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36857075265523386436132837 6910701612285634956774907)
      ·
        refine ⟨10366052418428452435162361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6910701612285634956774907 10366052418428452435162361)
        ·
          refine ⟨7774539313821339326371771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10366052418428452435162361 7774539313821339326371771)
          ·
            refine ⟨11661808970732008989557657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7774539313821339326371771 11661808970732008989557657)
            ·
              refine ⟨8746356728049006742168243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11661808970732008989557657 8746356728049006742168243)
              ·
                refine ⟨13119535092073510113252365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8746356728049006742168243 13119535092073510113252365)
                ·
                  refine ⟨4919825659527566292469637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13119535092073510113252365 4919825659527566292469637)
                  ·
                    refine ⟨922467311161418679838057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4919825659527566292469637 922467311161418679838057)
                    ·
                      rfl

theorem cell22_2694748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_2694748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694748 prefixEnd_2694748 := by exact prefixLift 2694748
  have htrace : WordTrace (prefixWord ++ tailWord_2694748) baseStart_2694748 baseEnd_2694748 := by
    simpa [prefixWord, tailWord_2694748, baseEnd_2694748] using wordTrace_append hprefix tailTrace_2694748
  have hstable : (prefixWord ++ tailWord_2694748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694748).length < 2 ^ (prefixWord ++ tailWord_2694748).sum := by decide
  have hdescent : baseEnd_2694748 < baseStart_2694748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694761 : List Nat := [1, 2, 1, 1, 1, 4, 4, 2, 1, 5]
def baseStart_2694761 : Nat := 118140960795 + 2694761 * 2 ^ 59
def prefixEnd_2694761 : Nat := 4983230072969 + 3 ^ 40 * 2694761 * 2
def baseEnd_2694761 : Nat := 922471761327090979263017

theorem tailTrace_2694761 : CollatzResearch.WordTrace tailWord_2694761 prefixEnd_2694761 922471761327090979263017 := by
  unfold tailWord_2694761
  simp only [CollatzResearch.WordTrace]
  refine ⟨98286008190348600383244137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65524005460232400255496091 98286008190348600383244137)
  ·
    refine ⟨73714506142761450287433103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98286008190348600383244137 73714506142761450287433103)
    ·
      refine ⟨110571759214142175431149655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73714506142761450287433103 110571759214142175431149655)
      ·
        refine ⟨165857638821213263146724483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110571759214142175431149655 165857638821213263146724483)
        ·
          refine ⟨248786458231819894720086725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165857638821213263146724483 248786458231819894720086725)
          ·
            refine ⟨46647460918466230260016261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 248786458231819894720086725 46647460918466230260016261)
            ·
              refine ⟨8746398922212418173753049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46647460918466230260016261 8746398922212418173753049)
              ·
                refine ⟨6559799191659313630314787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8746398922212418173753049 6559799191659313630314787)
                ·
                  refine ⟨9839698787488970445472181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6559799191659313630314787 9839698787488970445472181)
                  ·
                    refine ⟨922471761327090979263017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9839698787488970445472181 922471761327090979263017)
                    ·
                      rfl

theorem cell22_2694761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_2694761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694761 prefixEnd_2694761 := by exact prefixLift 2694761
  have htrace : WordTrace (prefixWord ++ tailWord_2694761) baseStart_2694761 baseEnd_2694761 := by
    simpa [prefixWord, tailWord_2694761, baseEnd_2694761] using wordTrace_append hprefix tailTrace_2694761
  have hstable : (prefixWord ++ tailWord_2694761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694761).length < 2 ^ (prefixWord ++ tailWord_2694761).sum := by decide
  have hdescent : baseEnd_2694761 < baseStart_2694761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694765 : List Nat := [1, 5, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_2694765 : Nat := 118140960795 + 2694765 * 2 ^ 59
def prefixEnd_2694765 : Nat := 4983230072969 + 3 ^ 40 * 2694765 * 2
def baseEnd_2694765 : Nat := 922473130608836302163005

theorem tailTrace_2694765 : CollatzResearch.WordTrace tailWord_2694765 prefixEnd_2694765 922473130608836302163005 := by
  unfold tailWord_2694765
  simp only [CollatzResearch.WordTrace]
  refine ⟨98286154082334109066389749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65524102721556072710926499 98286154082334109066389749)
  ·
    refine ⟨9214326945218822724974039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98286154082334109066389749 9214326945218822724974039)
    ·
      refine ⟨13821490417828234087461059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9214326945218822724974039 13821490417828234087461059)
      ·
        refine ⟨20732235626742351131191589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13821490417828234087461059 20732235626742351131191589)
        ·
          refine ⟨3887294180014190837098423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20732235626742351131191589 3887294180014190837098423)
          ·
            refine ⟨5830941270021286255647635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3887294180014190837098423 5830941270021286255647635)
            ·
              refine ⟨8746411905031929383471453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5830941270021286255647635 8746411905031929383471453)
              ·
                refine ⟨3279904464386973518801795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8746411905031929383471453 3279904464386973518801795)
                ·
                  refine ⟨4919856696580460278202693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3279904464386973518801795 4919856696580460278202693)
                  ·
                    refine ⟨922473130608836302163005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4919856696580460278202693 922473130608836302163005)
                    ·
                      rfl

theorem cell22_2694765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_2694765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694765 prefixEnd_2694765 := by exact prefixLift 2694765
  have htrace : WordTrace (prefixWord ++ tailWord_2694765) baseStart_2694765 baseEnd_2694765 := by
    simpa [prefixWord, tailWord_2694765, baseEnd_2694765] using wordTrace_append hprefix tailTrace_2694765
  have hstable : (prefixWord ++ tailWord_2694765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694765).length < 2 ^ (prefixWord ++ tailWord_2694765).sum := by decide
  have hdescent : baseEnd_2694765 < baseStart_2694765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694778 : List Nat := [3, 1, 1, 1, 1, 1, 1, 8, 2, 3]
def baseStart_2694778 : Nat := 118140960795 + 2694778 * 2 ^ 59
def prefixEnd_2694778 : Nat := 4983230072969 + 3 ^ 40 * 2694778 * 2
def baseEnd_2694778 : Nat := 922477580774508601587965

theorem tailTrace_2694778 : CollatzResearch.WordTrace tailWord_2694778 prefixEnd_2694778 922477580774508601587965 := by
  unfold tailWord_2694778
  simp only [CollatzResearch.WordTrace]
  refine ⟨24571657057821753071653247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65524418820858008191075325 24571657057821753071653247)
  ·
    refine ⟨36857485586732629607479871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24571657057821753071653247 36857485586732629607479871)
    ·
      refine ⟨55286228380098944411219807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36857485586732629607479871 55286228380098944411219807)
      ·
        refine ⟨82929342570148416616829711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55286228380098944411219807 82929342570148416616829711)
        ·
          refine ⟨124394013855222624925244567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82929342570148416616829711 124394013855222624925244567)
          ·
            refine ⟨186591020782833937387866851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124394013855222624925244567 186591020782833937387866851)
            ·
              refine ⟨279886531174250906081800277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186591020782833937387866851 279886531174250906081800277)
              ·
                refine ⟨3279920287198252805646097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 279886531174250906081800277 3279920287198252805646097)
                ·
                  refine ⟨2459940215398689604234573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3279920287198252805646097 2459940215398689604234573)
                  ·
                    refine ⟨922477580774508601587965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2459940215398689604234573 922477580774508601587965)
                    ·
                      rfl

theorem cell22_2694778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_2694778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694778 prefixEnd_2694778 := by exact prefixLift 2694778
  have htrace : WordTrace (prefixWord ++ tailWord_2694778) baseStart_2694778 baseEnd_2694778 := by
    simpa [prefixWord, tailWord_2694778, baseEnd_2694778] using wordTrace_append hprefix tailTrace_2694778
  have hstable : (prefixWord ++ tailWord_2694778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694778).length < 2 ^ (prefixWord ++ tailWord_2694778).sum := by decide
  have hdescent : baseEnd_2694778 < baseStart_2694778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694795 : List Nat := [1, 1, 1, 1, 4, 1, 7, 1, 2, 3]
def baseStart_2694795 : Nat := 118140960795 + 2694795 * 2 ^ 59
def prefixEnd_2694795 : Nat := 4983230072969 + 3 ^ 40 * 2694795 * 2
def baseEnd_2694795 : Nat := 922483400221926223912913

theorem tailTrace_2694795 : CollatzResearch.WordTrace tailWord_2694795 prefixEnd_2694795 922483400221926223912913 := by
  unfold tailWord_2694795
  simp only [CollatzResearch.WordTrace]
  refine ⟨98287248272225424189981839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65524832181483616126654559 98287248272225424189981839)
  ·
    refine ⟨147430872408338136284972759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98287248272225424189981839 147430872408338136284972759)
    ·
      refine ⟨221146308612507204427459139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147430872408338136284972759 221146308612507204427459139)
      ·
        refine ⟨331719462918760806641188709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221146308612507204427459139 331719462918760806641188709)
        ·
          refine ⟨62197399297267651245222883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 331719462918760806641188709 62197399297267651245222883)
          ·
            refine ⟨93296098945901476867834325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62197399297267651245222883 93296098945901476867834325)
            ·
              refine ⟨2186627319044565864089867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 93296098945901476867834325 2186627319044565864089867)
              ·
                refine ⟨3279940978566848796134801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2186627319044565864089867 3279940978566848796134801)
                ·
                  refine ⟨2459955733925136597101101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3279940978566848796134801 2459955733925136597101101)
                  ·
                    refine ⟨922483400221926223912913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2459955733925136597101101 922483400221926223912913)
                    ·
                      rfl

theorem cell22_2694795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 2, 3].length) (baseStart_2694795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694795 prefixEnd_2694795 := by exact prefixLift 2694795
  have htrace : WordTrace (prefixWord ++ tailWord_2694795) baseStart_2694795 baseEnd_2694795 := by
    simpa [prefixWord, tailWord_2694795, baseEnd_2694795] using wordTrace_append hprefix tailTrace_2694795
  have hstable : (prefixWord ++ tailWord_2694795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694795).length < 2 ^ (prefixWord ++ tailWord_2694795).sum := by decide
  have hdescent : baseEnd_2694795 < baseStart_2694795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694808 : List Nat := [2, 1, 2, 4, 1, 2, 4, 6]
def baseStart_2694808 : Nat := 118140960795 + 2694808 * 2 ^ 59
def prefixEnd_2694808 : Nat := 4983230072969 + 3 ^ 40 * 2694808 * 2
def baseEnd_2694808 : Nat := 102498650043066502593097

theorem tailTrace_2694808 : CollatzResearch.WordTrace tailWord_2694808 prefixEnd_2694808 102498650043066502593097 := by
  unfold tailWord_2694808
  simp only [CollatzResearch.WordTrace]
  refine ⟨49143861210589163705102539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65525148280785551606803385 49143861210589163705102539)
  ·
    refine ⟨73715791815883745557653809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49143861210589163705102539 73715791815883745557653809)
    ·
      refine ⟨55286843861912809168240357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73715791815883745557653809 55286843861912809168240357)
      ·
        refine ⟨10366283224108651719045067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55286843861912809168240357 10366283224108651719045067)
        ·
          refine ⟨15549424836162977578567601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10366283224108651719045067 15549424836162977578567601)
          ·
            refine ⟨11662068627122233183925701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15549424836162977578567601 11662068627122233183925701)
            ·
              refine ⟨2186637867585418721986069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11662068627122233183925701 2186637867585418721986069)
              ·
                refine ⟨102498650043066502593097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2186637867585418721986069 102498650043066502593097)
                ·
                  rfl

theorem cell22_2694808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 6].length) (baseStart_2694808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694808 prefixEnd_2694808 := by exact prefixLift 2694808
  have htrace : WordTrace (prefixWord ++ tailWord_2694808) baseStart_2694808 baseEnd_2694808 := by
    simpa [prefixWord, tailWord_2694808, baseEnd_2694808] using wordTrace_append hprefix tailTrace_2694808
  have hstable : (prefixWord ++ tailWord_2694808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694808).length < 2 ^ (prefixWord ++ tailWord_2694808).sum := by decide
  have hdescent : baseEnd_2694808 < baseStart_2694808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694840 : List Nat := [2, 1, 2, 1, 2, 1, 1, 8, 1, 3]
def baseStart_2694840 : Nat := 118140960795 + 2694840 * 2 ^ 59
def prefixEnd_2694840 : Nat := 4983230072969 + 3 ^ 40 * 2694840 * 2
def baseEnd_2694840 : Nat := 922498804641561106537775

theorem tailTrace_2694840 : CollatzResearch.WordTrace tailWord_2694840 prefixEnd_2694840 922498804641561106537775 := by
  unfold tailWord_2694840
  simp only [CollatzResearch.WordTrace]
  refine ⟨49144444778531198437684987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65525926371374931250246649 49144444778531198437684987)
  ·
    refine ⟨73716667167796797656527481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49144444778531198437684987 73716667167796797656527481)
    ·
      refine ⟨55287500375847598242395611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73716667167796797656527481 55287500375847598242395611)
      ·
        refine ⟨82931250563771397363593417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55287500375847598242395611 82931250563771397363593417)
        ·
          refine ⟨62198437922828548022695063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82931250563771397363593417 62198437922828548022695063)
          ·
            refine ⟨93297656884242822034042595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62198437922828548022695063 93297656884242822034042595)
            ·
              refine ⟨139946485326364233051063893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93297656884242822034042595 139946485326364233051063893)
              ·
                refine ⟨1639997874918330856067155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 139946485326364233051063893 1639997874918330856067155)
                ·
                  refine ⟨2459996812377496284100733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1639997874918330856067155 2459996812377496284100733)
                  ·
                    refine ⟨922498804641561106537775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2459996812377496284100733 922498804641561106537775)
                    ·
                      rfl

theorem cell22_2694840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 1, 3].length) (baseStart_2694840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694840 prefixEnd_2694840 := by exact prefixLift 2694840
  have htrace : WordTrace (prefixWord ++ tailWord_2694840) baseStart_2694840 baseEnd_2694840 := by
    simpa [prefixWord, tailWord_2694840, baseEnd_2694840] using wordTrace_append hprefix tailTrace_2694840
  have hstable : (prefixWord ++ tailWord_2694840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694840).length < 2 ^ (prefixWord ++ tailWord_2694840).sum := by decide
  have hdescent : baseEnd_2694840 < baseStart_2694840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694887 : List Nat := [1, 1, 5, 4, 1, 1, 2, 2, 5]
def baseStart_2694887 : Nat := 118140960795 + 2694887 * 2 ^ 59
def prefixEnd_2694887 : Nat := 4983230072969 + 3 ^ 40 * 2694887 * 2
def baseEnd_2694887 : Nat := 307504964567356216870877

theorem tailTrace_2694887 : CollatzResearch.WordTrace tailWord_2694887 prefixEnd_2694887 307504964567356216870877 := by
  unfold tailWord_2694887
  simp only [CollatzResearch.WordTrace]
  refine ⟨98290603787892123902330915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65527069191928082601553943 98290603787892123902330915)
  ·
    refine ⟨147435905681838185853496373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98290603787892123902330915 147435905681838185853496373)
    ·
      refine ⟨13822116157672329923765285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147435905681838185853496373 13822116157672329923765285)
      ·
        refine ⟨2591646779563561860705991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13822116157672329923765285 2591646779563561860705991)
        ·
          refine ⟨3887470169345342791058987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2591646779563561860705991 3887470169345342791058987)
          ·
            refine ⟨5831205254018014186588481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3887470169345342791058987 5831205254018014186588481)
            ·
              refine ⟨4373403940513510639941361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5831205254018014186588481 4373403940513510639941361)
              ·
                refine ⟨3280052955385132979956021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4373403940513510639941361 3280052955385132979956021)
                ·
                  refine ⟨307504964567356216870877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3280052955385132979956021 307504964567356216870877)
                  ·
                    rfl

theorem cell22_2694887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 5].length) (baseStart_2694887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694887 prefixEnd_2694887 := by exact prefixLift 2694887
  have htrace : WordTrace (prefixWord ++ tailWord_2694887) baseStart_2694887 baseEnd_2694887 := by
    simpa [prefixWord, tailWord_2694887, baseEnd_2694887] using wordTrace_append hprefix tailTrace_2694887
  have hstable : (prefixWord ++ tailWord_2694887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694887).length < 2 ^ (prefixWord ++ tailWord_2694887).sum := by decide
  have hdescent : baseEnd_2694887 < baseStart_2694887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694898 : List Nat := [3, 2, 1, 3, 1, 1, 2, 3, 6]
def baseStart_2694898 : Nat := 118140960795 + 2694898 * 2 ^ 59
def prefixEnd_2694898 : Nat := 4983230072969 + 3 ^ 40 * 2694898 * 2
def baseEnd_2694898 : Nat := 307506219742289429529199

theorem tailTrace_2694898 : CollatzResearch.WordTrace tailWord_2694898 prefixEnd_2694898 307506219742289429529199 := by
  unfold tailWord_2694898
  simp only [CollatzResearch.WordTrace]
  refine ⟨24572751247713068195245337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65527336660568181853987565 24572751247713068195245337)
  ·
    refine ⟨18429563435784801146434003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24572751247713068195245337 18429563435784801146434003)
    ·
      refine ⟨27644345153677201719651005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18429563435784801146434003 27644345153677201719651005)
      ·
        refine ⟨10366629432628950644869127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27644345153677201719651005 10366629432628950644869127)
        ·
          refine ⟨15549944148943425967303691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10366629432628950644869127 15549944148943425967303691)
          ·
            refine ⟨23324916223415138950955537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15549944148943425967303691 23324916223415138950955537)
            ·
              refine ⟨17493687167561354213216653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23324916223415138950955537 17493687167561354213216653)
              ·
                refine ⟨6560132687835507829956245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17493687167561354213216653 6560132687835507829956245)
                ·
                  refine ⟨307506219742289429529199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6560132687835507829956245 307506219742289429529199)
                  ·
                    rfl

theorem cell22_2694898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_2694898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694898 prefixEnd_2694898 := by exact prefixLift 2694898
  have htrace : WordTrace (prefixWord ++ tailWord_2694898) baseStart_2694898 baseEnd_2694898 := by
    simpa [prefixWord, tailWord_2694898, baseEnd_2694898] using wordTrace_append hprefix tailTrace_2694898
  have hstable : (prefixWord ++ tailWord_2694898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694898).length < 2 ^ (prefixWord ++ tailWord_2694898).sum := by decide
  have hdescent : baseEnd_2694898 < baseStart_2694898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694913 : List Nat := [1, 2, 4, 1, 1, 1, 3, 3, 1, 5]
def baseStart_2694913 : Nat := 118140960795 + 2694913 * 2 ^ 59
def prefixEnd_2694913 : Nat := 4983230072969 + 3 ^ 40 * 2694913 * 2
def baseEnd_2694913 : Nat := 922523794033413249462551

theorem tailTrace_2694913 : CollatzResearch.WordTrace tailWord_2694913 prefixEnd_2694913 922523794033413249462551 := by
  unfold tailWord_2694913
  simp only [CollatzResearch.WordTrace]
  refine ⟨98291552085797930342777393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65527701390531953561851595 98291552085797930342777393)
  ·
    refine ⟨73718664064348447757083045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98291552085797930342777393 73718664064348447757083045)
    ·
      refine ⟨13822249512065333954453071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73718664064348447757083045 13822249512065333954453071)
      ·
        refine ⟨20733374268098000931679607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13822249512065333954453071 20733374268098000931679607)
        ·
          refine ⟨31100061402147001397519411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20733374268098000931679607 31100061402147001397519411)
          ·
            refine ⟨46650092103220502096279117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31100061402147001397519411 46650092103220502096279117)
            ·
              refine ⟨17493784538707688286104669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46650092103220502096279117 17493784538707688286104669)
              ·
                refine ⟨6560169202015383107289251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17493784538707688286104669 6560169202015383107289251)
                ·
                  refine ⟨9840253803023074660933877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6560169202015383107289251 9840253803023074660933877)
                  ·
                    refine ⟨922523794033413249462551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9840253803023074660933877 922523794033413249462551)
                    ·
                      rfl

theorem cell22_2694913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_2694913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694913 prefixEnd_2694913 := by exact prefixLift 2694913
  have htrace : WordTrace (prefixWord ++ tailWord_2694913) baseStart_2694913 baseEnd_2694913 := by
    simpa [prefixWord, tailWord_2694913, baseEnd_2694913] using wordTrace_append hprefix tailTrace_2694913
  have hstable : (prefixWord ++ tailWord_2694913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694913).length < 2 ^ (prefixWord ++ tailWord_2694913).sum := by decide
  have hdescent : baseEnd_2694913 < baseStart_2694913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694925 : List Nat := [1, 7, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2694925 : Nat := 118140960795 + 2694925 * 2 ^ 59
def prefixEnd_2694925 : Nat := 4983230072969 + 3 ^ 40 * 2694925 * 2
def baseEnd_2694925 : Nat := 922527901878649218162515

theorem tailTrace_2694925 : CollatzResearch.WordTrace tailWord_2694925 prefixEnd_2694925 922527901878649218162515 := by
  unfold tailWord_2694925
  simp only [CollatzResearch.WordTrace]
  refine ⟨98291989761754456392214229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65527993174502970928142819 98291989761754456392214229)
  ·
    refine ⟨2303718510041120071692521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 98291989761754456392214229 2303718510041120071692521)
    ·
      refine ⟨1727788882530840053769391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2303718510041120071692521 1727788882530840053769391)
      ·
        refine ⟨2591683323796260080654087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1727788882530840053769391 2591683323796260080654087)
        ·
          refine ⟨3887524985694390120981131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2591683323796260080654087 3887524985694390120981131)
          ·
            refine ⟨5831287478541585181471697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3887524985694390120981131 5831287478541585181471697)
            ·
              refine ⟨4373465608906188886103773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5831287478541585181471697 4373465608906188886103773)
              ·
                refine ⟨1640049603339820832288915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4373465608906188886103773 1640049603339820832288915)
                ·
                  refine ⟨2460074405009731248433373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640049603339820832288915 2460074405009731248433373)
                  ·
                    refine ⟨922527901878649218162515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2460074405009731248433373 922527901878649218162515)
                    ·
                      rfl

theorem cell22_2694925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2694925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2694925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2694925 prefixEnd_2694925 := by exact prefixLift 2694925
  have htrace : WordTrace (prefixWord ++ tailWord_2694925) baseStart_2694925 baseEnd_2694925 := by
    simpa [prefixWord, tailWord_2694925, baseEnd_2694925] using wordTrace_append hprefix tailTrace_2694925
  have hstable : (prefixWord ++ tailWord_2694925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694925).length < 2 ^ (prefixWord ++ tailWord_2694925).sum := by decide
  have hdescent : baseEnd_2694925 < baseStart_2694925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695009 : List Nat := [1, 2, 3, 1, 1, 1, 7, 2, 1, 3]
def baseStart_2695009 : Nat := 118140960795 + 2695009 * 2 ^ 59
def prefixEnd_2695009 : Nat := 4983230072969 + 3 ^ 40 * 2695009 * 2
def baseEnd_2695009 : Nat := 922556656795300999062257

theorem tailTrace_2695009 : CollatzResearch.WordTrace tailWord_2695009 prefixEnd_2695009 922556656795300999062257 := by
  unfold tailWord_2695009
  simp only [CollatzResearch.WordTrace]
  refine ⟨98295053493450138738272081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65530035662300092492181387 98295053493450138738272081)
  ·
    refine ⟨73721290120087604053704061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98295053493450138738272081 73721290120087604053704061)
    ·
      refine ⟨27645483795032851520139023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73721290120087604053704061 27645483795032851520139023)
      ·
        refine ⟨41468225692549277280208535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27645483795032851520139023 41468225692549277280208535)
        ·
          refine ⟨62202338538823915920312803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41468225692549277280208535 62202338538823915920312803)
          ·
            refine ⟨93303507808235873880469205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62202338538823915920312803 93303507808235873880469205)
            ·
              refine ⟨2186800964255528294073497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 93303507808235873880469205 2186800964255528294073497)
              ·
                refine ⟨1640100723191646220555123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2186800964255528294073497 1640100723191646220555123)
                ·
                  refine ⟨2460151084787469330832685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640100723191646220555123 2460151084787469330832685)
                  ·
                    refine ⟨922556656795300999062257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2460151084787469330832685 922556656795300999062257)
                    ·
                      rfl

theorem cell22_2695009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_2695009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695009 prefixEnd_2695009 := by exact prefixLift 2695009
  have htrace : WordTrace (prefixWord ++ tailWord_2695009) baseStart_2695009 baseEnd_2695009 := by
    simpa [prefixWord, tailWord_2695009, baseEnd_2695009] using wordTrace_append hprefix tailTrace_2695009
  have hstable : (prefixWord ++ tailWord_2695009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695009).length < 2 ^ (prefixWord ++ tailWord_2695009).sum := by decide
  have hdescent : baseEnd_2695009 < baseStart_2695009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695022 : List Nat := [4, 1, 2, 3, 1, 2, 1, 3, 5]
def baseStart_2695022 : Nat := 118140960795 + 2695022 * 2 ^ 59
def prefixEnd_2695022 : Nat := 4983230072969 + 3 ^ 40 * 2695022 * 2
def baseEnd_2695022 : Nat := 307520368986991099495739

theorem tailTrace_2695022 : CollatzResearch.WordTrace tailWord_2695022 prefixEnd_2695022 307520368986991099495739 := by
  unfold tailWord_2695022
  simp only [CollatzResearch.WordTrace]
  refine ⟨12286940955300380244811915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65530351761602027972330213 12286940955300380244811915)
  ·
    refine ⟨18430411432950570367217873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12286940955300380244811915 18430411432950570367217873)
    ·
      refine ⟨13822808574712927775413405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18430411432950570367217873 13822808574712927775413405)
      ·
        refine ⟨5183553215517347915780027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13822808574712927775413405 5183553215517347915780027)
        ·
          refine ⟨7775329823276021873670041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5183553215517347915780027 7775329823276021873670041)
          ·
            refine ⟨5831497367457016405252531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7775329823276021873670041 5831497367457016405252531)
            ·
              refine ⟨8747246051185524607878797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5831497367457016405252531 8747246051185524607878797)
              ·
                refine ⟨3280217269194571727954549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8747246051185524607878797 3280217269194571727954549)
                ·
                  refine ⟨307520368986991099495739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3280217269194571727954549 307520368986991099495739)
                  ·
                    rfl

theorem cell22_2695022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_2695022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695022 prefixEnd_2695022 := by exact prefixLift 2695022
  have htrace : WordTrace (prefixWord ++ tailWord_2695022) baseStart_2695022 baseEnd_2695022 := by
    simpa [prefixWord, tailWord_2695022, baseEnd_2695022] using wordTrace_append hprefix tailTrace_2695022
  have hstable : (prefixWord ++ tailWord_2695022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695022).length < 2 ^ (prefixWord ++ tailWord_2695022).sum := by decide
  have hdescent : baseEnd_2695022 < baseStart_2695022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695033 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 8]
def baseStart_2695033 : Nat := 118140960795 + 2695033 * 2 ^ 59
def prefixEnd_2695033 : Nat := 4983230072969 + 3 ^ 40 * 2695033 * 2
def baseEnd_2695033 : Nat := 307521624161924312154061

theorem tailTrace_2695033 : CollatzResearch.WordTrace tailWord_2695033 prefixEnd_2695033 307521624161924312154061 := by
  unfold tailWord_2695033
  simp only [CollatzResearch.WordTrace]
  refine ⟨98295928845363190837145753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65530619230242127224763835 98295928845363190837145753)
  ·
    refine ⟨73721946634022393127859315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98295928845363190837145753 73721946634022393127859315)
    ·
      refine ⟨110582919951033589691788973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73721946634022393127859315 110582919951033589691788973)
      ·
        refine ⟨41468594981637596134420865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110582919951033589691788973 41468594981637596134420865)
        ·
          refine ⟨31101446236228197100815649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41468594981637596134420865 31101446236228197100815649)
          ·
            refine ⟨23326084677171147825611737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31101446236228197100815649 23326084677171147825611737)
            ·
              refine ⟨17494563507878360869208803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23326084677171147825611737 17494563507878360869208803)
              ·
                refine ⟨26241845261817541303813205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17494563507878360869208803 26241845261817541303813205)
                ·
                  refine ⟨307521624161924312154061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26241845261817541303813205 307521624161924312154061)
                  ·
                    rfl

theorem cell22_2695033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 8].length) (baseStart_2695033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695033 prefixEnd_2695033 := by exact prefixLift 2695033
  have htrace : WordTrace (prefixWord ++ tailWord_2695033) baseStart_2695033 baseEnd_2695033 := by
    simpa [prefixWord, tailWord_2695033, baseEnd_2695033] using wordTrace_append hprefix tailTrace_2695033
  have hstable : (prefixWord ++ tailWord_2695033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695033).length < 2 ^ (prefixWord ++ tailWord_2695033).sum := by decide
  have hdescent : baseEnd_2695033 < baseStart_2695033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695065 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 4, 3]
def baseStart_2695065 : Nat := 118140960795 + 2695065 * 2 ^ 59
def prefixEnd_2695065 : Nat := 4983230072969 + 3 ^ 40 * 2695065 * 2
def baseEnd_2695065 : Nat := 922575826739735519662085

theorem tailTrace_2695065 : CollatzResearch.WordTrace tailWord_2695065 prefixEnd_2695065 922575826739735519662085 := by
  unfold tailWord_2695065
  simp only [CollatzResearch.WordTrace]
  refine ⟨98297095981247260302310649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65531397320831506868207099 98297095981247260302310649)
  ·
    refine ⟨73722821985935445226732987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98297095981247260302310649 73722821985935445226732987)
    ·
      refine ⟨110584232978903167840099481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73722821985935445226732987 110584232978903167840099481)
      ·
        refine ⟨82938174734177375880074611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110584232978903167840099481 82938174734177375880074611)
        ·
          refine ⟨124407262101266063820111917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82938174734177375880074611 124407262101266063820111917)
          ·
            refine ⟨46652723287974773932541969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124407262101266063820111917 46652723287974773932541969)
            ·
              refine ⟨34989542465981080449406477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46652723287974773932541969 34989542465981080449406477)
              ·
                refine ⟨13121078424742905168527429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34989542465981080449406477 13121078424742905168527429)
                ·
                  refine ⟨2460202204639294719098893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13121078424742905168527429 2460202204639294719098893)
                  ·
                    refine ⟨922575826739735519662085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2460202204639294719098893 922575826739735519662085)
                    ·
                      rfl

theorem cell22_2695065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 3].length) (baseStart_2695065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695065 prefixEnd_2695065 := by exact prefixLift 2695065
  have htrace : WordTrace (prefixWord ++ tailWord_2695065) baseStart_2695065 baseEnd_2695065 := by
    simpa [prefixWord, tailWord_2695065, baseEnd_2695065] using wordTrace_append hprefix tailTrace_2695065
  have hstable : (prefixWord ++ tailWord_2695065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695065).length < 2 ^ (prefixWord ++ tailWord_2695065).sum := by decide
  have hdescent : baseEnd_2695065 < baseStart_2695065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695127 : List Nat := [1, 1, 3, 2, 1, 1, 6, 1, 3, 3]
def baseStart_2695127 : Nat := 118140960795 + 2695127 * 2 ^ 59
def prefixEnd_2695127 : Nat := 4983230072969 + 3 ^ 40 * 2695127 * 2
def baseEnd_2695127 : Nat := 922597050606788024611895

theorem tailTrace_2695127 : CollatzResearch.WordTrace tailWord_2695127 prefixEnd_2695127 922597050606788024611895 := by
  unfold tailWord_2695127
  simp only [CollatzResearch.WordTrace]
  refine ⟨98299357307022644891067635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65532904871348429927378423 98299357307022644891067635)
  ·
    refine ⟨147449035960533967336601453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98299357307022644891067635 147449035960533967336601453)
    ·
      refine ⟨55293388485200237751225545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147449035960533967336601453 55293388485200237751225545)
      ·
        refine ⟨41470041363900178313419159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55293388485200237751225545 41470041363900178313419159)
        ·
          refine ⟨62205062045850267470128739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41470041363900178313419159 62205062045850267470128739)
          ·
            refine ⟨93307593068775401205193109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62205062045850267470128739 93307593068775401205193109)
            ·
              refine ⟨4373793425098846931493427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93307593068775401205193109 4373793425098846931493427)
              ·
                refine ⟨6560690137648270397240141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4373793425098846931493427 6560690137648270397240141)
                ·
                  refine ⟨2460258801618101398965053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6560690137648270397240141 2460258801618101398965053)
                  ·
                    refine ⟨922597050606788024611895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2460258801618101398965053 922597050606788024611895)
                    ·
                      rfl

theorem cell22_2695127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_2695127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695127 prefixEnd_2695127 := by exact prefixLift 2695127
  have htrace : WordTrace (prefixWord ++ tailWord_2695127) baseStart_2695127 baseEnd_2695127 := by
    simpa [prefixWord, tailWord_2695127, baseEnd_2695127] using wordTrace_append hprefix tailTrace_2695127
  have hstable : (prefixWord ++ tailWord_2695127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695127).length < 2 ^ (prefixWord ++ tailWord_2695127).sum := by decide
  have hdescent : baseEnd_2695127 < baseStart_2695127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695161 : List Nat := [1, 2, 1, 3, 1, 6, 1, 3, 1, 3]
def baseStart_2695161 : Nat := 118140960795 + 2695161 * 2 ^ 59
def prefixEnd_2695161 : Nat := 4983230072969 + 3 ^ 40 * 2695161 * 2
def baseEnd_2695161 : Nat := 922608689501623269261791

theorem tailTrace_2695161 : CollatzResearch.WordTrace tailWord_2695161 prefixEnd_2695161 922608689501623269261791 := by
  unfold tailWord_2695161
  simp only [CollatzResearch.WordTrace]
  refine ⟨98300597388899468697805337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65533731592599645798536891 98300597388899468697805337)
  ·
    refine ⟨73725448041674601523354003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98300597388899468697805337 73725448041674601523354003)
    ·
      refine ⟨110588172062511902285031005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73725448041674601523354003 110588172062511902285031005)
      ·
        refine ⟨41470564523441963356886627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110588172062511902285031005 41470564523441963356886627)
        ·
          refine ⟨62205846785162945035329941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41470564523441963356886627 62205846785162945035329941)
          ·
            refine ⟨2915899068054513048531091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62205846785162945035329941 2915899068054513048531091)
            ·
              refine ⟨4373848602081769572796637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2915899068054513048531091 4373848602081769572796637)
              ·
                refine ⟨1640193225780663589798739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4373848602081769572796637 1640193225780663589798739)
                ·
                  refine ⟨2460289838670995384698109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640193225780663589798739 2460289838670995384698109)
                  ·
                    refine ⟨922608689501623269261791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2460289838670995384698109 922608689501623269261791)
                    ·
                      rfl

theorem cell22_2695161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 1, 3].length) (baseStart_2695161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695161 prefixEnd_2695161 := by exact prefixLift 2695161
  have htrace : WordTrace (prefixWord ++ tailWord_2695161) baseStart_2695161 baseEnd_2695161 := by
    simpa [prefixWord, tailWord_2695161, baseEnd_2695161] using wordTrace_append hprefix tailTrace_2695161
  have hstable : (prefixWord ++ tailWord_2695161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695161).length < 2 ^ (prefixWord ++ tailWord_2695161).sum := by decide
  have hdescent : baseEnd_2695161 < baseStart_2695161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695178 : List Nat := [3, 1, 2, 2, 4, 1, 3, 2, 1, 3]
def baseStart_2695178 : Nat := 118140960795 + 2695178 * 2 ^ 59
def prefixEnd_2695178 : Nat := 4983230072969 + 3 ^ 40 * 2695178 * 2
def baseEnd_2695178 : Nat := 922614508949040891586739

theorem tailTrace_2695178 : CollatzResearch.WordTrace tailWord_2695178 prefixEnd_2695178 922614508949040891586739 := by
  unfold tailWord_2695178
  simp only [CollatzResearch.WordTrace]
  refine ⟨24575304357459470150293547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65534144953225253734116125 24575304357459470150293547)
  ·
    refine ⟨36862956536189205225440321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24575304357459470150293547 36862956536189205225440321)
    ·
      refine ⟨27647217402141903919080241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36862956536189205225440321 27647217402141903919080241)
      ·
        refine ⟨20735413051606427939310181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27647217402141903919080241 20735413051606427939310181)
        ·
          refine ⟨3887889947176205238620659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20735413051606427939310181 3887889947176205238620659)
          ·
            refine ⟨5831834920764307857930989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3887889947176205238620659 5831834920764307857930989)
            ·
              refine ⟨2186938095286615446724121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5831834920764307857930989 2186938095286615446724121)
              ·
                refine ⟨1640203571464961585043091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2186938095286615446724121 1640203571464961585043091)
                ·
                  refine ⟨2460305357197442377564637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640203571464961585043091 2460305357197442377564637)
                  ·
                    refine ⟨922614508949040891586739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2460305357197442377564637 922614508949040891586739)
                    ·
                      rfl

theorem cell22_2695178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_2695178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695178 prefixEnd_2695178 := by exact prefixLift 2695178
  have htrace : WordTrace (prefixWord ++ tailWord_2695178) baseStart_2695178 baseEnd_2695178 := by
    simpa [prefixWord, tailWord_2695178, baseEnd_2695178] using wordTrace_append hprefix tailTrace_2695178
  have hstable : (prefixWord ++ tailWord_2695178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695178).length < 2 ^ (prefixWord ++ tailWord_2695178).sum := by decide
  have hdescent : baseEnd_2695178 < baseStart_2695178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695191 : List Nat := [1, 1, 3, 5, 2, 2, 2, 1, 5]
def baseStart_2695191 : Nat := 118140960795 + 2695191 * 2 ^ 59
def prefixEnd_2695191 : Nat := 4983230072969 + 3 ^ 40 * 2695191 * 2
def baseEnd_2695191 : Nat := 307539653038237730337233

theorem tailTrace_2695191 : CollatzResearch.WordTrace tailWord_2695191 prefixEnd_2695191 307539653038237730337233 := by
  unfold tailWord_2695191
  simp only [CollatzResearch.WordTrace]
  refine ⟨98301691578790783821397427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65534461052527189214264951 98301691578790783821397427)
  ·
    refine ⟨147452537368186175732096141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98301691578790783821397427 147452537368186175732096141)
    ·
      refine ⟨55294701513069815899536053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147452537368186175732096141 55294701513069815899536053)
      ·
        refine ⟨5183878266850295240581505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55294701513069815899536053 5183878266850295240581505)
        ·
          refine ⟨3887908700137721430436129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5183878266850295240581505 3887908700137721430436129)
          ·
            refine ⟨2915931525103291072827097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3887908700137721430436129 2915931525103291072827097)
            ·
              refine ⟨2186948643827468304620323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2915931525103291072827097 2186948643827468304620323)
              ·
                refine ⟨3280422965741202456930485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2186948643827468304620323 3280422965741202456930485)
                ·
                  refine ⟨307539653038237730337233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3280422965741202456930485 307539653038237730337233)
                  ·
                    rfl

theorem cell22_2695191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 5].length) (baseStart_2695191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695191 prefixEnd_2695191 := by exact prefixLift 2695191
  have htrace : WordTrace (prefixWord ++ tailWord_2695191) baseStart_2695191 baseEnd_2695191 := by
    simpa [prefixWord, tailWord_2695191, baseEnd_2695191] using wordTrace_append hprefix tailTrace_2695191
  have hstable : (prefixWord ++ tailWord_2695191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695191).length < 2 ^ (prefixWord ++ tailWord_2695191).sum := by decide
  have hdescent : baseEnd_2695191 < baseStart_2695191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695204 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_2695204 : Nat := 118140960795 + 2695204 * 2 ^ 59
def prefixEnd_2695204 : Nat := 4983230072969 + 3 ^ 40 * 2695204 * 2
def baseEnd_2695204 : Nat := 922623409280385490436659

theorem tailTrace_2695204 : CollatzResearch.WordTrace tailWord_2695204 prefixEnd_2695204 922623409280385490436659 := by
  unfold tailWord_2695204
  simp only [CollatzResearch.WordTrace]
  refine ⟨49151082863871843520810333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65534777151829124694413777 49151082863871843520810333)
  ·
    refine ⟨18431656073951941320303875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49151082863871843520810333 18431656073951941320303875)
    ·
      refine ⟨27647484110927911980455813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18431656073951941320303875 27647484110927911980455813)
      ·
        refine ⟨5183903270798983496335465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27647484110927911980455813 5183903270798983496335465)
        ·
          refine ⟨3887927453099237622251599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5183903270798983496335465 3887927453099237622251599)
          ·
            refine ⟨5831891179648856433377399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3887927453099237622251599 5831891179648856433377399)
            ·
              refine ⟨8747836769473284650066099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5831891179648856433377399 8747836769473284650066099)
              ·
                refine ⟨13121755154209926975099149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8747836769473284650066099 13121755154209926975099149)
                ·
                  refine ⟨4920658182828722615662181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13121755154209926975099149 4920658182828722615662181)
                  ·
                    refine ⟨922623409280385490436659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4920658182828722615662181 922623409280385490436659)
                    ·
                      rfl

theorem cell22_2695204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_2695204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695204 prefixEnd_2695204 := by exact prefixLift 2695204
  have htrace : WordTrace (prefixWord ++ tailWord_2695204) baseStart_2695204 baseEnd_2695204 := by
    simpa [prefixWord, tailWord_2695204, baseEnd_2695204] using wordTrace_append hprefix tailTrace_2695204
  have hstable : (prefixWord ++ tailWord_2695204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695204).length < 2 ^ (prefixWord ++ tailWord_2695204).sum := by decide
  have hdescent : baseEnd_2695204 < baseStart_2695204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695217 : List Nat := [1, 2, 2, 3, 1, 4, 1, 2, 1, 5]
def baseStart_2695217 : Nat := 118140960795 + 2695217 * 2 ^ 59
def prefixEnd_2695217 : Nat := 4983230072969 + 3 ^ 40 * 2695217 * 2
def baseEnd_2695217 : Nat := 922627859446057789861619

theorem tailTrace_2695217 : CollatzResearch.WordTrace tailWord_2695217 prefixEnd_2695217 922627859446057789861619 := by
  unfold tailWord_2695217
  simp only [CollatzResearch.WordTrace]
  refine ⟨98302639876696590261843905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65535093251131060174562603 98302639876696590261843905)
  ·
    refine ⟨73726979907522442696382929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98302639876696590261843905 73726979907522442696382929)
    ·
      refine ⟨55295234930641832022287197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73726979907522442696382929 55295234930641832022287197)
      ·
        refine ⟨20735713098990687008357699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55295234930641832022287197 20735713098990687008357699)
        ·
          refine ⟨31103569648486030512536549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20735713098990687008357699 31103569648486030512536549)
          ·
            refine ⟨5831919309091130721100603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31103569648486030512536549 5831919309091130721100603)
            ·
              refine ⟨8747878963636696081650905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5831919309091130721100603 8747878963636696081650905)
              ·
                refine ⟨6560909222727522061238179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8747878963636696081650905 6560909222727522061238179)
                ·
                  refine ⟨9841363834091283091857269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6560909222727522061238179 9841363834091283091857269)
                  ·
                    refine ⟨922627859446057789861619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9841363834091283091857269 922627859446057789861619)
                    ·
                      rfl

theorem cell22_2695217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_2695217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695217 prefixEnd_2695217 := by exact prefixLift 2695217
  have htrace : WordTrace (prefixWord ++ tailWord_2695217) baseStart_2695217 baseEnd_2695217 := by
    simpa [prefixWord, tailWord_2695217, baseEnd_2695217] using wordTrace_append hprefix tailTrace_2695217
  have hstable : (prefixWord ++ tailWord_2695217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695217).length < 2 ^ (prefixWord ++ tailWord_2695217).sum := by decide
  have hdescent : baseEnd_2695217 < baseStart_2695217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695232 : List Nat := [2, 1, 1, 2, 2, 4, 2, 2, 2, 4]
def baseStart_2695232 : Nat := 118140960795 + 2695232 * 2 ^ 59
def prefixEnd_2695232 : Nat := 4983230072969 + 3 ^ 40 * 2695232 * 2
def baseEnd_2695232 : Nat := 922632994252602750736573

theorem tailTrace_2695232 : CollatzResearch.WordTrace tailWord_2695232 prefixEnd_2695232 922632994252602750736573 := by
  unfold tailWord_2695232
  simp only [CollatzResearch.WordTrace]
  refine ⟨49151593485821123911819975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65535457981094831882426633 49151593485821123911819975)
  ·
    refine ⟨73727390228731685867729963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49151593485821123911819975 73727390228731685867729963)
    ·
      refine ⟨110591085343097528801594945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73727390228731685867729963 110591085343097528801594945)
      ·
        refine ⟨82943314007323146601196209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110591085343097528801594945 82943314007323146601196209)
        ·
          refine ⟨62207485505492359950897157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82943314007323146601196209 62207485505492359950897157)
          ·
            refine ⟨11663903532279817490793217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62207485505492359950897157 11663903532279817490793217)
            ·
              refine ⟨8747927649209863118094913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11663903532279817490793217 8747927649209863118094913)
              ·
                refine ⟨6560945736907397338571185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8747927649209863118094913 6560945736907397338571185)
                ·
                  refine ⟨4920709302680548003928389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6560945736907397338571185 4920709302680548003928389)
                  ·
                    refine ⟨922632994252602750736573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4920709302680548003928389 922632994252602750736573)
                    ·
                      rfl

theorem cell22_2695232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_2695232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695232 prefixEnd_2695232 := by exact prefixLift 2695232
  have htrace : WordTrace (prefixWord ++ tailWord_2695232) baseStart_2695232 baseEnd_2695232 := by
    simpa [prefixWord, tailWord_2695232, baseEnd_2695232] using wordTrace_append hprefix tailTrace_2695232
  have hstable : (prefixWord ++ tailWord_2695232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695232).length < 2 ^ (prefixWord ++ tailWord_2695232).sum := by decide
  have hdescent : baseEnd_2695232 < baseStart_2695232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695292 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 7]
def baseStart_2695292 : Nat := 118140960795 + 2695292 * 2 ^ 59
def prefixEnd_2695292 : Nat := 4983230072969 + 3 ^ 40 * 2695292 * 2
def baseEnd_2695292 : Nat := 307551177826260864745463

theorem tailTrace_2695292 : CollatzResearch.WordTrace tailWord_2695292 prefixEnd_2695292 307551177826260864745463 := by
  unfold tailWord_2695292
  simp only [CollatzResearch.WordTrace]
  refine ⟨49152687675712439035412065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65536916900949918713882753 49152687675712439035412065)
  ·
    refine ⟨36864515756784329276559049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49152687675712439035412065 36864515756784329276559049)
    ·
      refine ⟨27648386817588246957419287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36864515756784329276559049 27648386817588246957419287)
      ·
        refine ⟨41472580226382370436128931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27648386817588246957419287 41472580226382370436128931)
        ·
          refine ⟨62208870339573555654193397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41472580226382370436128931 62208870339573555654193397)
          ·
            refine ⟨5832081594335020842580631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62208870339573555654193397 5832081594335020842580631)
            ·
              refine ⟨8748122391502531263870947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5832081594335020842580631 8748122391502531263870947)
              ·
                refine ⟨13122183587253796895806421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8748122391502531263870947 13122183587253796895806421)
                ·
                  refine ⟨307551177826260864745463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13122183587253796895806421 307551177826260864745463)
                  ·
                    rfl

theorem cell22_2695292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_2695292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695292 prefixEnd_2695292 := by exact prefixLift 2695292
  have htrace : WordTrace (prefixWord ++ tailWord_2695292) baseStart_2695292 baseEnd_2695292 := by
    simpa [prefixWord, tailWord_2695292, baseEnd_2695292] using wordTrace_append hprefix tailTrace_2695292
  have hstable : (prefixWord ++ tailWord_2695292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695292).length < 2 ^ (prefixWord ++ tailWord_2695292).sum := by decide
  have hdescent : baseEnd_2695292 < baseStart_2695292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695330 : List Nat := [3, 3, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_2695330 : Nat := 118140960795 + 2695330 * 2 ^ 59
def prefixEnd_2695330 : Nat := 4983230072969 + 3 ^ 40 * 2695330 * 2
def baseEnd_2695330 : Nat := 922666541655363161786273

theorem tailTrace_2695330 : CollatzResearch.WordTrace tailWord_2695330 prefixEnd_2695330 922666541655363161786273 := by
  unfold tailWord_2695330
  simp only [CollatzResearch.WordTrace]
  refine ⟨24576690331321802640176861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65537840883524807040471629 24576690331321802640176861)
  ·
    refine ⟨9216258874245675990066323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24576690331321802640176861 9216258874245675990066323)
    ·
      refine ⟨13824388311368513985099485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9216258874245675990066323 13824388311368513985099485)
      ·
        refine ⟨5184145616763192744412307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13824388311368513985099485 5184145616763192744412307)
        ·
          refine ⟨7776218425144789116618461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5184145616763192744412307 7776218425144789116618461)
          ·
            refine ⟨2916081909429295918731923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7776218425144789116618461 2916081909429295918731923)
            ·
              refine ⟨4374122864143943878097885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2916081909429295918731923 4374122864143943878097885)
              ·
                refine ⟨1640296074053978954286707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4374122864143943878097885 1640296074053978954286707)
                ·
                  refine ⟨2460444111080968431430061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640296074053978954286707 2460444111080968431430061)
                  ·
                    refine ⟨922666541655363161786273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2460444111080968431430061 922666541655363161786273)
                    ·
                      rfl

theorem cell22_2695330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_2695330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695330 prefixEnd_2695330 := by exact prefixLift 2695330
  have htrace : WordTrace (prefixWord ++ tailWord_2695330) baseStart_2695330 baseEnd_2695330 := by
    simpa [prefixWord, tailWord_2695330, baseEnd_2695330] using wordTrace_append hprefix tailTrace_2695330
  have hstable : (prefixWord ++ tailWord_2695330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695330).length < 2 ^ (prefixWord ++ tailWord_2695330).sum := by decide
  have hdescent : baseEnd_2695330 < baseStart_2695330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695354 : List Nat := [3, 1, 1, 1, 2, 2, 2, 6, 4]
def baseStart_2695354 : Nat := 118140960795 + 2695354 * 2 ^ 59
def prefixEnd_2695354 : Nat := 4983230072969 + 3 ^ 40 * 2695354 * 2
def baseEnd_2695354 : Nat := 307558252448611699728733

theorem tailTrace_2695354 : CollatzResearch.WordTrace tailWord_2695354 prefixEnd_2695354 307558252448611699728733 := by
  unfold tailWord_2695354
  simp only [CollatzResearch.WordTrace]
  refine ⟨24576909169300065664895279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65538424451466841773054077 24576909169300065664895279)
  ·
    refine ⟨36865363753950098497342919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24576909169300065664895279 36865363753950098497342919)
    ·
      refine ⟨55298045630925147746014379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36865363753950098497342919 55298045630925147746014379)
      ·
        refine ⟨82947068446387721619021569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55298045630925147746014379 82947068446387721619021569)
        ·
          refine ⟨62210301334790791214266177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82947068446387721619021569 62210301334790791214266177)
          ·
            refine ⟨46657726001093093410699633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62210301334790791214266177 46657726001093093410699633)
            ·
              refine ⟨34993294500819820058024725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46657726001093093410699633 34993294500819820058024725)
              ·
                refine ⟨1640310679725929065219909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34993294500819820058024725 1640310679725929065219909)
                ·
                  refine ⟨307558252448611699728733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1640310679725929065219909 307558252448611699728733)
                  ·
                    rfl

theorem cell22_2695354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_2695354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695354 prefixEnd_2695354 := by exact prefixLift 2695354
  have htrace : WordTrace (prefixWord ++ tailWord_2695354) baseStart_2695354 baseEnd_2695354 := by
    simpa [prefixWord, tailWord_2695354, baseEnd_2695354] using wordTrace_append hprefix tailTrace_2695354
  have hstable : (prefixWord ++ tailWord_2695354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695354).length < 2 ^ (prefixWord ++ tailWord_2695354).sum := by decide
  have hdescent : baseEnd_2695354 < baseStart_2695354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695384 : List Nat := [2, 1, 2, 2, 4, 1, 1, 3, 2, 4]
def baseStart_2695384 : Nat := 118140960795 + 2695384 * 2 ^ 59
def prefixEnd_2695384 : Nat := 4983230072969 + 3 ^ 40 * 2695384 * 2
def baseEnd_2695384 : Nat := 922685026958925020936107

theorem tailTrace_2695384 : CollatzResearch.WordTrace tailWord_2695384 prefixEnd_2695384 922685026958925020936107 := by
  unfold tailWord_2695384
  simp only [CollatzResearch.WordTrace]
  refine ⟨49154365433545788891586603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65539153911394385188782137 49154365433545788891586603)
  ·
    refine ⟨73731548150318683337379905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49154365433545788891586603 73731548150318683337379905)
    ·
      refine ⟨55298661112739012503034929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73731548150318683337379905 55298661112739012503034929)
      ·
        refine ⟨41473995834554259377276197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55298661112739012503034929 41473995834554259377276197)
        ·
          refine ⟨7776374218978923633239287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41473995834554259377276197 7776374218978923633239287)
          ·
            refine ⟨11664561328468385449858931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7776374218978923633239287 11664561328468385449858931)
            ·
              refine ⟨17496841992702578174788397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11664561328468385449858931 17496841992702578174788397)
              ·
                refine ⟨6561315747263466815545649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17496841992702578174788397 6561315747263466815545649)
                ·
                  refine ⟨4920986810447600111659237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6561315747263466815545649 4920986810447600111659237)
                  ·
                    refine ⟨922685026958925020936107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4920986810447600111659237 922685026958925020936107)
                    ·
                      rfl

theorem cell22_2695384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_2695384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695384 prefixEnd_2695384 := by exact prefixLift 2695384
  have htrace : WordTrace (prefixWord ++ tailWord_2695384) baseStart_2695384 baseEnd_2695384 := by
    simpa [prefixWord, tailWord_2695384, baseEnd_2695384] using wordTrace_append hprefix tailTrace_2695384
  have hstable : (prefixWord ++ tailWord_2695384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695384).length < 2 ^ (prefixWord ++ tailWord_2695384).sum := by decide
  have hdescent : baseEnd_2695384 < baseStart_2695384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695405 : List Nat := [1, 5, 1, 2, 3, 2, 2, 2, 4]
def baseStart_2695405 : Nat := 118140960795 + 2695405 * 2 ^ 59
def prefixEnd_2695405 : Nat := 4983230072969 + 3 ^ 40 * 2695405 * 2
def baseEnd_2695405 : Nat := 307564071896029322053681

theorem tailTrace_2695405 : CollatzResearch.WordTrace tailWord_2695405 prefixEnd_2695405 307564071896029322053681 := by
  unfold tailWord_2695405
  simp only [CollatzResearch.WordTrace]
  refine ⟨98309496800015498369687669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65539664533343665579791779 98309496800015498369687669)
  ·
    refine ⟨9216515325001452972158219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98309496800015498369687669 9216515325001452972158219)
    ·
      refine ⟨13824772987502179458237329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9216515325001452972158219 13824772987502179458237329)
      ·
        refine ⟨10368579740626634593677997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13824772987502179458237329 10368579740626634593677997)
        ·
          refine ⟨3888217402734987972629249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10368579740626634593677997 3888217402734987972629249)
          ·
            refine ⟨2916163052051240979471937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3888217402734987972629249 2916163052051240979471937)
            ·
              refine ⟨2187122289038430734603953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2916163052051240979471937 2187122289038430734603953)
              ·
                refine ⟨1640341716778823050952965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2187122289038430734603953 1640341716778823050952965)
                ·
                  refine ⟨307564071896029322053681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1640341716778823050952965 307564071896029322053681)
                  ·
                    rfl

theorem cell22_2695405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_2695405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695405 prefixEnd_2695405 := by exact prefixLift 2695405
  have htrace : WordTrace (prefixWord ++ tailWord_2695405) baseStart_2695405 baseEnd_2695405 := by
    simpa [prefixWord, tailWord_2695405, baseEnd_2695405] using wordTrace_append hprefix tailTrace_2695405
  have hstable : (prefixWord ++ tailWord_2695405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695405).length < 2 ^ (prefixWord ++ tailWord_2695405).sum := by decide
  have hdescent : baseEnd_2695405 < baseStart_2695405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695448 : List Nat := [2, 1, 2, 3, 1, 2, 4, 3, 1, 3]
def baseStart_2695448 : Nat := 118140960795 + 2695448 * 2 ^ 59
def prefixEnd_2695448 : Nat := 4983230072969 + 3 ^ 40 * 2695448 * 2
def baseEnd_2695448 : Nat := 922706935466850187335911

theorem tailTrace_2695448 : CollatzResearch.WordTrace tailWord_2695448 prefixEnd_2695448 922706935466850187335911 := by
  unfold tailWord_2695448
  simp only [CollatzResearch.WordTrace]
  refine ⟨49155532569429858356751499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65540710092573144475668665 49155532569429858356751499)
  ·
    refine ⟨73733298854144787535127249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49155532569429858356751499 73733298854144787535127249)
    ·
      refine ⟨55299974140608590651345437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73733298854144787535127249 55299974140608590651345437)
      ·
        refine ⟨20737490302728221494254539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55299974140608590651345437 20737490302728221494254539)
        ·
          refine ⟨31106235454092332241381809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20737490302728221494254539 31106235454092332241381809)
          ·
            refine ⟨23329676590569249181036357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31106235454092332241381809 23329676590569249181036357)
            ·
              refine ⟨4374314360731734221444317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23329676590569249181036357 4374314360731734221444317)
              ·
                refine ⟨1640367885274400333041619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4374314360731734221444317 1640367885274400333041619)
                ·
                  refine ⟨2460551827911600499562429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640367885274400333041619 2460551827911600499562429)
                  ·
                    refine ⟨922706935466850187335911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2460551827911600499562429 922706935466850187335911)
                    ·
                      rfl

theorem cell22_2695448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 1, 3].length) (baseStart_2695448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695448 prefixEnd_2695448 := by exact prefixLift 2695448
  have htrace : WordTrace (prefixWord ++ tailWord_2695448) baseStart_2695448 baseEnd_2695448 := by
    simpa [prefixWord, tailWord_2695448, baseEnd_2695448] using wordTrace_append hprefix tailTrace_2695448
  have hstable : (prefixWord ++ tailWord_2695448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695448).length < 2 ^ (prefixWord ++ tailWord_2695448).sum := by decide
  have hdescent : baseEnd_2695448 < baseStart_2695448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695476 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_2695476 : Nat := 118140960795 + 2695476 * 2 ^ 59
def prefixEnd_2695476 : Nat := 4983230072969 + 3 ^ 40 * 2695476 * 2
def baseEnd_2695476 : Nat := 922716520439067447635825

theorem tailTrace_2695476 : CollatzResearch.WordTrace tailWord_2695476 prefixEnd_2695476 922716520439067447635825 := by
  unfold tailWord_2695476
  simp only [CollatzResearch.WordTrace]
  refine ⟨49156043191379138747761141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65541390921838851663681521 49156043191379138747761141)
  ·
    refine ⟨4608379049191794257602607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49156043191379138747761141 4608379049191794257602607)
    ·
      refine ⟨6912568573787691386403911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4608379049191794257602607 6912568573787691386403911)
      ·
        refine ⟨10368852860681537079605867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6912568573787691386403911 10368852860681537079605867)
        ·
          refine ⟨15553279291022305619408801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10368852860681537079605867 15553279291022305619408801)
          ·
            refine ⟨11664959468266729214556601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15553279291022305619408801 11664959468266729214556601)
            ·
              refine ⟨8748719601200046910917451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11664959468266729214556601 8748719601200046910917451)
              ·
                refine ⟨13123079401800070366376177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8748719601200046910917451 13123079401800070366376177)
                ·
                  refine ⟨9842309551350052774782133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13123079401800070366376177 9842309551350052774782133)
                  ·
                    refine ⟨922716520439067447635825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9842309551350052774782133 922716520439067447635825)
                    ·
                      rfl

theorem cell22_2695476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_2695476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695476 prefixEnd_2695476 := by exact prefixLift 2695476
  have htrace : WordTrace (prefixWord ++ tailWord_2695476) baseStart_2695476 baseEnd_2695476 := by
    simpa [prefixWord, tailWord_2695476, baseEnd_2695476] using wordTrace_append hprefix tailTrace_2695476
  have hstable : (prefixWord ++ tailWord_2695476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695476).length < 2 ^ (prefixWord ++ tailWord_2695476).sum := by decide
  have hdescent : baseEnd_2695476 < baseStart_2695476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695519 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 4, 4]
def baseStart_2695519 : Nat := 118140960795 + 2695519 * 2 ^ 59
def prefixEnd_2695519 : Nat := 4983230072969 + 3 ^ 40 * 2695519 * 2
def baseEnd_2695519 : Nat := 922731240217829668810693

theorem tailTrace_2695519 : CollatzResearch.WordTrace tailWord_2695519 prefixEnd_2695519 922731240217829668810693 := by
  unfold tailWord_2695519
  simp only [CollatzResearch.WordTrace]
  refine ⟨98313654721602495839337611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65542436481068330559558407 98313654721602495839337611)
  ·
    refine ⟨147470482082403743759006417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98313654721602495839337611 147470482082403743759006417)
    ·
      refine ⟨110602861561802807819254813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147470482082403743759006417 110602861561802807819254813)
      ·
        refine ⟨41476073085676052932220555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110602861561802807819254813 41476073085676052932220555)
        ·
          refine ⟨62214109628514079398330833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41476073085676052932220555 62214109628514079398330833)
          ·
            refine ⟨46660582221385559548748125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62214109628514079398330833 46660582221385559548748125)
            ·
              refine ⟨17497718333019584830780547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46660582221385559548748125 17497718333019584830780547)
              ·
                refine ⟨26246577499529377246170821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17497718333019584830780547 26246577499529377246170821)
                ·
                  refine ⟨4921233281161758233657029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26246577499529377246170821 4921233281161758233657029)
                  ·
                    refine ⟨922731240217829668810693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4921233281161758233657029 922731240217829668810693)
                    ·
                      rfl

theorem cell22_2695519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_2695519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695519 prefixEnd_2695519 := by exact prefixLift 2695519
  have htrace : WordTrace (prefixWord ++ tailWord_2695519) baseStart_2695519 baseEnd_2695519 := by
    simpa [prefixWord, tailWord_2695519, baseEnd_2695519] using wordTrace_append hprefix tailTrace_2695519
  have hstable : (prefixWord ++ tailWord_2695519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695519).length < 2 ^ (prefixWord ++ tailWord_2695519).sum := by decide
  have hdescent : baseEnd_2695519 < baseStart_2695519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695523 : List Nat := [1, 1, 1, 5, 2, 1, 5, 2, 4]
def baseStart_2695523 : Nat := 118140960795 + 2695523 * 2 ^ 59
def prefixEnd_2695523 : Nat := 4983230072969 + 3 ^ 40 * 2695523 * 2
def baseEnd_2695523 : Nat := 307577536499858330570227

theorem tailTrace_2695523 : CollatzResearch.WordTrace tailWord_2695523 prefixEnd_2695523 307577536499858330570227 := by
  unfold tailWord_2695523
  simp only [CollatzResearch.WordTrace]
  refine ⟨98313800613588004522483223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65542533742392003014988815 98313800613588004522483223)
  ·
    refine ⟨147470700920382006783724835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98313800613588004522483223 147470700920382006783724835)
    ·
      refine ⟨221206051380573010175587253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147470700920382006783724835 221206051380573010175587253)
      ·
        refine ⟨20738067316928719703961305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 221206051380573010175587253 20738067316928719703961305)
        ·
          refine ⟨15553550487696539777970979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20738067316928719703961305 15553550487696539777970979)
          ·
            refine ⟨23330325731544809666956469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15553550487696539777970979 23330325731544809666956469)
            ·
              refine ⟨2187218037332325906277169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23330325731544809666956469 2187218037332325906277169)
              ·
                refine ⟨1640413527999244429707877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2187218037332325906277169 1640413527999244429707877)
                ·
                  refine ⟨307577536499858330570227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1640413527999244429707877 307577536499858330570227)
                  ·
                    rfl

theorem cell22_2695523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 4].length) (baseStart_2695523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695523 prefixEnd_2695523 := by exact prefixLift 2695523
  have htrace : WordTrace (prefixWord ++ tailWord_2695523) baseStart_2695523 baseEnd_2695523 := by
    simpa [prefixWord, tailWord_2695523, baseEnd_2695523] using wordTrace_append hprefix tailTrace_2695523
  have hstable : (prefixWord ++ tailWord_2695523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695523).length < 2 ^ (prefixWord ++ tailWord_2695523).sum := by decide
  have hdescent : baseEnd_2695523 < baseStart_2695523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695538 : List Nat := [3, 2, 1, 2, 1, 4, 1, 3, 2, 3]
def baseStart_2695538 : Nat := 118140960795 + 2695538 * 2 ^ 59
def prefixEnd_2695538 : Nat := 4983230072969 + 3 ^ 40 * 2695538 * 2
def baseEnd_2695538 : Nat := 922737744306119952585635

theorem tailTrace_2695538 : CollatzResearch.WordTrace tailWord_2695538 prefixEnd_2695538 922737744306119952585635 := by
  unfold tailWord_2695538
  simp only [CollatzResearch.WordTrace]
  refine ⟨24578586927133415521069817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65542898472355774722852845 24578586927133415521069817)
  ·
    refine ⟨18433940195350061640802363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24578586927133415521069817 18433940195350061640802363)
    ·
      refine ⟨27650910293025092461203545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18433940195350061640802363 27650910293025092461203545)
      ·
        refine ⟨20738182719768819345902659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27650910293025092461203545 20738182719768819345902659)
        ·
          refine ⟨31107274079653229018853989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20738182719768819345902659 31107274079653229018853989)
          ·
            refine ⟨5832613889934980441035123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31107274079653229018853989 5832613889934980441035123)
            ·
              refine ⟨8748920834902470661552685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5832613889934980441035123 8748920834902470661552685)
              ·
                refine ⟨3280845313088426498082257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8748920834902470661552685 3280845313088426498082257)
                ·
                  refine ⟨2460633984816319873561693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3280845313088426498082257 2460633984816319873561693)
                  ·
                    refine ⟨922737744306119952585635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2460633984816319873561693 922737744306119952585635)
                    ·
                      rfl

theorem cell22_2695538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_2695538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695538 prefixEnd_2695538 := by exact prefixLift 2695538
  have htrace : WordTrace (prefixWord ++ tailWord_2695538) baseStart_2695538 baseEnd_2695538 := by
    simpa [prefixWord, tailWord_2695538, baseEnd_2695538] using wordTrace_append hprefix tailTrace_2695538
  have hstable : (prefixWord ++ tailWord_2695538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695538).length < 2 ^ (prefixWord ++ tailWord_2695538).sum := by decide
  have hdescent : baseEnd_2695538 < baseStart_2695538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695542 : List Nat := [5, 1, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_2695542 : Nat := 118140960795 + 2695542 * 2 ^ 59
def prefixEnd_2695542 : Nat := 4983230072969 + 3 ^ 40 * 2695542 * 2
def baseEnd_2695542 : Nat := 922739113587865275485623

theorem tailTrace_2695542 : CollatzResearch.WordTrace tailWord_2695542 prefixEnd_2695542 922739113587865275485623 := by
  unfold tailWord_2695542
  simp only [CollatzResearch.WordTrace]
  refine ⟨6144655850032448172964055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65542995733679447178283253 6144655850032448172964055)
  ·
    refine ⟨9216983775048672259446083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6144655850032448172964055 9216983775048672259446083)
    ·
      refine ⟨13825475662573008389169125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9216983775048672259446083 13825475662573008389169125)
      ·
        refine ⟨2592276686732439072969211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13825475662573008389169125 2592276686732439072969211)
        ·
          refine ⟨3888415030098658609453817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2592276686732439072969211 3888415030098658609453817)
          ·
            refine ⟨2916311272573993957090363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3888415030098658609453817 2916311272573993957090363)
            ·
              refine ⟨4374466908860990935635545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2916311272573993957090363 4374466908860990935635545)
              ·
                refine ⟨3280850181645743201726659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4374466908860990935635545 3280850181645743201726659)
                ·
                  refine ⟨4921275272468614802589989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3280850181645743201726659 4921275272468614802589989)
                  ·
                    refine ⟨922739113587865275485623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4921275272468614802589989 922739113587865275485623)
                    ·
                      rfl

theorem cell22_2695542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_2695542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695542 prefixEnd_2695542 := by exact prefixLift 2695542
  have htrace : WordTrace (prefixWord ++ tailWord_2695542) baseStart_2695542 baseEnd_2695542 := by
    simpa [prefixWord, tailWord_2695542, baseEnd_2695542] using wordTrace_append hprefix tailTrace_2695542
  have hstable : (prefixWord ++ tailWord_2695542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695542).length < 2 ^ (prefixWord ++ tailWord_2695542).sum := by decide
  have hdescent : baseEnd_2695542 < baseStart_2695542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695553 : List Nat := [1, 2, 4, 3, 1, 2, 2, 1, 2, 4]
def baseStart_2695553 : Nat := 118140960795 + 2695553 * 2 ^ 59
def prefixEnd_2695553 : Nat := 4983230072969 + 3 ^ 40 * 2695553 * 2
def baseEnd_2695553 : Nat := 922742879112664913460589

theorem tailTrace_2695553 : CollatzResearch.WordTrace tailWord_2695553 prefixEnd_2695553 922742879112664913460589 := by
  unfold tailWord_2695553
  simp only [CollatzResearch.WordTrace]
  refine ⟨98314894803479319646075313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65543263202319546430716875 98314894803479319646075313)
  ·
    refine ⟨73736171102609489734556485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98314894803479319646075313 73736171102609489734556485)
    ·
      refine ⟨13825532081739279325229341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73736171102609489734556485 13825532081739279325229341)
      ·
        refine ⟨5184574530652229746961003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13825532081739279325229341 5184574530652229746961003)
        ·
          refine ⟨7776861795978344620441505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5184574530652229746961003 7776861795978344620441505)
          ·
            refine ⟨5832646346983758465331129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7776861795978344620441505 5832646346983758465331129)
            ·
              refine ⟨4374484760237818848998347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5832646346983758465331129 4374484760237818848998347)
              ·
                refine ⟨6561727140356728273497521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4374484760237818848998347 6561727140356728273497521)
                ·
                  refine ⟨4921295355267546205123141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6561727140356728273497521 4921295355267546205123141)
                  ·
                    refine ⟨922742879112664913460589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4921295355267546205123141 922742879112664913460589)
                    ·
                      rfl

theorem cell22_2695553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_2695553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695553 prefixEnd_2695553 := by exact prefixLift 2695553
  have htrace : WordTrace (prefixWord ++ tailWord_2695553) baseStart_2695553 baseEnd_2695553 := by
    simpa [prefixWord, tailWord_2695553, baseEnd_2695553] using wordTrace_append hprefix tailTrace_2695553
  have hstable : (prefixWord ++ tailWord_2695553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695553).length < 2 ^ (prefixWord ++ tailWord_2695553).sum := by decide
  have hdescent : baseEnd_2695553 < baseStart_2695553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695574 : List Nat := [5, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_2695574 : Nat := 118140960795 + 2695574 * 2 ^ 59
def prefixEnd_2695574 : Nat := 4983230072969 + 3 ^ 40 * 2695574 * 2
def baseEnd_2695574 : Nat := 307583355947275952895175

theorem tailTrace_2695574 : CollatzResearch.WordTrace tailWord_2695574 prefixEnd_2695574 307583355947275952895175 := by
  unfold tailWord_2695574
  simp only [CollatzResearch.WordTrace]
  refine ⟨6144728796025202514536861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65543773824268826821726517 6144728796025202514536861)
  ·
    refine ⟨2304273298509450942951323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6144728796025202514536861 2304273298509450942951323)
    ·
      refine ⟨3456409947764176414426985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2304273298509450942951323 3456409947764176414426985)
      ·
        refine ⟨2592307460823132310820239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3456409947764176414426985 2592307460823132310820239)
        ·
          refine ⟨3888461191234698466230359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2592307460823132310820239 3888461191234698466230359)
          ·
            refine ⟨5832691786852047699345539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3888461191234698466230359 5832691786852047699345539)
            ·
              refine ⟨8749037680278071549018309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5832691786852047699345539 8749037680278071549018309)
              ·
                refine ⟨1640444565052138415440933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8749037680278071549018309 1640444565052138415440933)
                ·
                  refine ⟨307583355947275952895175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1640444565052138415440933 307583355947275952895175)
                  ·
                    rfl

theorem cell22_2695574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_2695574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695574 prefixEnd_2695574 := by exact prefixLift 2695574
  have htrace : WordTrace (prefixWord ++ tailWord_2695574) baseStart_2695574 baseEnd_2695574 := by
    simpa [prefixWord, tailWord_2695574, baseEnd_2695574] using wordTrace_append hprefix tailTrace_2695574
  have hstable : (prefixWord ++ tailWord_2695574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695574).length < 2 ^ (prefixWord ++ tailWord_2695574).sum := by decide
  have hdescent : baseEnd_2695574 < baseStart_2695574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695585 : List Nat := [1, 2, 3, 5, 2, 1, 1, 7]
def baseStart_2695585 : Nat := 118140960795 + 2695585 * 2 ^ 59
def prefixEnd_2695585 : Nat := 4983230072969 + 3 ^ 40 * 2695585 * 2
def baseEnd_2695585 : Nat := 102528203707403055184499

theorem tailTrace_2695585 : CollatzResearch.WordTrace tailWord_2695585 prefixEnd_2695585 102528203707403055184499 := by
  unfold tailWord_2695585
  simp only [CollatzResearch.WordTrace]
  refine ⟨98316061939363389111240209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65544041292908926074160139 98316061939363389111240209)
  ·
    refine ⟨73737046454522541833430157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98316061939363389111240209 73737046454522541833430157)
    ·
      refine ⟨27651392420445953187536309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73737046454522541833430157 27651392420445953187536309)
      ·
        refine ⟨2592318039416808111331529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27651392420445953187536309 2592318039416808111331529)
        ·
          refine ⟨1944238529562606083498647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2592318039416808111331529 1944238529562606083498647)
          ·
            refine ⟨2916357794343909125247971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944238529562606083498647 2916357794343909125247971)
            ·
              refine ⟨4374536691515863687871957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2916357794343909125247971 4374536691515863687871957)
              ·
                refine ⟨102528203707403055184499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4374536691515863687871957 102528203707403055184499)
                ·
                  rfl

theorem cell22_2695585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 7].length) (baseStart_2695585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695585 prefixEnd_2695585 := by exact prefixLift 2695585
  have htrace : WordTrace (prefixWord ++ tailWord_2695585) baseStart_2695585 baseEnd_2695585 := by
    simpa [prefixWord, tailWord_2695585, baseEnd_2695585] using wordTrace_append hprefix tailTrace_2695585
  have hstable : (prefixWord ++ tailWord_2695585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695585).length < 2 ^ (prefixWord ++ tailWord_2695585).sum := by decide
  have hdescent : baseEnd_2695585 < baseStart_2695585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695604 : List Nat := [2, 5, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_2695604 : Nat := 118140960795 + 2695604 * 2 ^ 59
def prefixEnd_2695604 : Nat := 4983230072969 + 3 ^ 40 * 2695604 * 2
def baseEnd_2695604 : Nat := 922760337454917780435433

theorem tailTrace_2695604 : CollatzResearch.WordTrace tailWord_2695604 prefixEnd_2695604 922760337454917780435433 := by
  unfold tailWord_2695604
  simp only [CollatzResearch.WordTrace]
  refine ⟨49158377463147277678090933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65544503284196370237454577 49158377463147277678090933)
  ·
    refine ⟨4608597887170057282321025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49158377463147277678090933 4608597887170057282321025)
    ·
      refine ⟨3456448415377542961740769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4608597887170057282321025 3456448415377542961740769)
      ·
        refine ⟨2592336311533157221305577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3456448415377542961740769 2592336311533157221305577)
        ·
          refine ⟨1944252233649867915979183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2592336311533157221305577 1944252233649867915979183)
          ·
            refine ⟨2916378350474801873968775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944252233649867915979183 2916378350474801873968775)
            ·
              refine ⟨4374567525712202810953163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2916378350474801873968775 4374567525712202810953163)
              ·
                refine ⟨6561851288568304216429745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4374567525712202810953163 6561851288568304216429745)
                ·
                  refine ⟨4921388466426228162322309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6561851288568304216429745 4921388466426228162322309)
                  ·
                    refine ⟨922760337454917780435433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4921388466426228162322309 922760337454917780435433)
                    ·
                      rfl

theorem cell22_2695604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_2695604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695604 prefixEnd_2695604 := by exact prefixLift 2695604
  have htrace : WordTrace (prefixWord ++ tailWord_2695604) baseStart_2695604 baseEnd_2695604 := by
    simpa [prefixWord, tailWord_2695604, baseEnd_2695604] using wordTrace_append hprefix tailTrace_2695604
  have hstable : (prefixWord ++ tailWord_2695604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695604).length < 2 ^ (prefixWord ++ tailWord_2695604).sum := by decide
  have hdescent : baseEnd_2695604 < baseStart_2695604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695639 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 2, 9]
def baseStart_2695639 : Nat := 118140960795 + 2695639 * 2 ^ 59
def prefixEnd_2695639 : Nat := 4983230072969 + 3 ^ 40 * 2695639 * 2
def baseEnd_2695639 : Nat := 922772318670189355810325

theorem tailTrace_2695639 : CollatzResearch.WordTrace tailWord_2695639 prefixEnd_2695639 922772318670189355810325 := by
  unfold tailWord_2695639
  simp only [CollatzResearch.WordTrace]
  refine ⟨98318031481167756333705971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65545354320778504222470647 98318031481167756333705971)
  ·
    refine ⟨147477047221751634500558957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98318031481167756333705971 147477047221751634500558957)
    ·
      refine ⟨55303892708156862937709609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147477047221751634500558957 55303892708156862937709609)
      ·
        refine ⟨41477919531117647203282207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55303892708156862937709609 41477919531117647203282207)
        ·
          refine ⟨62216879296676470804923311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41477919531117647203282207 62216879296676470804923311)
          ·
            refine ⟨93325318945014706207384967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62216879296676470804923311 93325318945014706207384967)
            ·
              refine ⟨139987978417522059311077451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93325318945014706207384967 139987978417522059311077451)
              ·
                refine ⟨209981967626283088966616177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139987978417522059311077451 209981967626283088966616177)
                ·
                  refine ⟨157486475719712316724962133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209981967626283088966616177 157486475719712316724962133)
                  ·
                    refine ⟨922772318670189355810325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 157486475719712316724962133 922772318670189355810325)
                    ·
                      rfl

theorem cell22_2695639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_2695639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695639 prefixEnd_2695639 := by exact prefixLift 2695639
  have htrace : WordTrace (prefixWord ++ tailWord_2695639) baseStart_2695639 baseEnd_2695639 := by
    simpa [prefixWord, tailWord_2695639, baseEnd_2695639] using wordTrace_append hprefix tailTrace_2695639
  have hstable : (prefixWord ++ tailWord_2695639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695639).length < 2 ^ (prefixWord ++ tailWord_2695639).sum := by decide
  have hdescent : baseEnd_2695639 < baseStart_2695639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695641 : List Nat := [1, 2, 1, 2, 4, 1, 4, 1, 6]
def baseStart_2695641 : Nat := 118140960795 + 2695641 * 2 ^ 59
def prefixEnd_2695641 : Nat := 4983230072969 + 3 ^ 40 * 2695641 * 2
def baseEnd_2695641 : Nat := 307591001103687339086773

theorem tailTrace_2695641 : CollatzResearch.WordTrace tailWord_2695641 prefixEnd_2695641 307591001103687339086773 := by
  unfold tailWord_2695641
  simp only [CollatzResearch.WordTrace]
  refine ⟨98318104427160510675278777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65545402951440340450185851 98318104427160510675278777)
  ·
    refine ⟨73738578320370383006459083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98318104427160510675278777 73738578320370383006459083)
    ·
      refine ⟨110607867480555574509688625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73738578320370383006459083 110607867480555574509688625)
      ·
        refine ⟨82955900610416680882266469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110607867480555574509688625 82955900610416680882266469)
        ·
          refine ⟨15554231364453127665424963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82955900610416680882266469 15554231364453127665424963)
          ·
            refine ⟨23331347046679691498137445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15554231364453127665424963 23331347046679691498137445)
            ·
              refine ⟨4374627571252442155900771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23331347046679691498137445 4374627571252442155900771)
              ·
                refine ⟨6561941356878663233851157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4374627571252442155900771 6561941356878663233851157)
                ·
                  refine ⟨307591001103687339086773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6561941356878663233851157 307591001103687339086773)
                  ·
                    rfl

theorem cell22_2695641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 6].length) (baseStart_2695641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695641 prefixEnd_2695641 := by exact prefixLift 2695641
  have htrace : WordTrace (prefixWord ++ tailWord_2695641) baseStart_2695641 baseEnd_2695641 := by
    simpa [prefixWord, tailWord_2695641, baseEnd_2695641] using wordTrace_append hprefix tailTrace_2695641
  have hstable : (prefixWord ++ tailWord_2695641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695641).length < 2 ^ (prefixWord ++ tailWord_2695641).sum := by decide
  have hdescent : baseEnd_2695641 < baseStart_2695641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695735 : List Nat := [1, 1, 3, 1, 2, 3, 2, 5, 1, 3]
def baseStart_2695735 : Nat := 118140960795 + 2695735 * 2 ^ 59
def prefixEnd_2695735 : Nat := 4983230072969 + 3 ^ 40 * 2695735 * 2
def baseEnd_2695735 : Nat := 922805181432077105410031

theorem tailTrace_2695735 : CollatzResearch.WordTrace tailWord_2695735 prefixEnd_2695735 922805181432077105410031 := by
  unfold tailWord_2695735
  simp only [CollatzResearch.WordTrace]
  refine ⟨98321532888819964729200659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65547688592546643152800439 98321532888819964729200659)
  ·
    refine ⟨147482299333229947093800989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98321532888819964729200659 147482299333229947093800989)
    ·
      refine ⟨55305862249961230160175371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147482299333229947093800989 55305862249961230160175371)
      ·
        refine ⟨82958793374941845240263057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55305862249961230160175371 82958793374941845240263057)
        ·
          refine ⟨62219095031206383930197293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82958793374941845240263057 62219095031206383930197293)
          ·
            refine ⟨23332160636702393973823985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62219095031206383930197293 23332160636702393973823985)
            ·
              refine ⟨17499120477526795480367989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23332160636702393973823985 17499120477526795480367989)
              ·
                refine ⟨1640542544768137076284499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17499120477526795480367989 1640542544768137076284499)
                ·
                  refine ⟨2460813817152205614426749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640542544768137076284499 2460813817152205614426749)
                  ·
                    refine ⟨922805181432077105410031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2460813817152205614426749 922805181432077105410031)
                    ·
                      rfl

theorem cell22_2695735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 1, 3].length) (baseStart_2695735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695735 prefixEnd_2695735 := by exact prefixLift 2695735
  have htrace : WordTrace (prefixWord ++ tailWord_2695735) baseStart_2695735 baseEnd_2695735 := by
    simpa [prefixWord, tailWord_2695735, baseEnd_2695735] using wordTrace_append hprefix tailTrace_2695735
  have hstable : (prefixWord ++ tailWord_2695735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695735).length < 2 ^ (prefixWord ++ tailWord_2695735).sum := by decide
  have hdescent : baseEnd_2695735 < baseStart_2695735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695750 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_2695750 : Nat := 118140960795 + 2695750 * 2 ^ 59
def prefixEnd_2695750 : Nat := 4983230072969 + 3 ^ 40 * 2695750 * 2
def baseEnd_2695750 : Nat := 922810316238622066284985

theorem tailTrace_2695750 : CollatzResearch.WordTrace tailWord_2695750 prefixEnd_2695750 922810316238622066284985 := by
  unfold tailWord_2695750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3072564999492675696593647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65548053322510414860664469 3072564999492675696593647)
  ·
    refine ⟨4608847499239013544890471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3072564999492675696593647 4608847499239013544890471)
    ·
      refine ⟨6913271248858520317335707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4608847499239013544890471 6913271248858520317335707)
      ·
        refine ⟨10369906873287780476003561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6913271248858520317335707 10369906873287780476003561)
        ·
          refine ⟨7777430154965835357002671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10369906873287780476003561 7777430154965835357002671)
          ·
            refine ⟨11666145232448753035504007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7777430154965835357002671 11666145232448753035504007)
            ·
              refine ⟨17499217848673129553256011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11666145232448753035504007 17499217848673129553256011)
              ·
                refine ⟨26248826773009694329884017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17499217848673129553256011 26248826773009694329884017)
                ·
                  refine ⟨19686620079757270747413013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26248826773009694329884017 19686620079757270747413013)
                  ·
                    refine ⟨922810316238622066284985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19686620079757270747413013 922810316238622066284985)
                    ·
                      rfl

theorem cell22_2695750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_2695750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695750 prefixEnd_2695750 := by exact prefixLift 2695750
  have htrace : WordTrace (prefixWord ++ tailWord_2695750) baseStart_2695750 baseEnd_2695750 := by
    simpa [prefixWord, tailWord_2695750, baseEnd_2695750] using wordTrace_append hprefix tailTrace_2695750
  have hstable : (prefixWord ++ tailWord_2695750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695750).length < 2 ^ (prefixWord ++ tailWord_2695750).sum := by decide
  have hdescent : baseEnd_2695750 < baseStart_2695750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695776 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 8]
def baseStart_2695776 : Nat := 118140960795 + 2695776 * 2 ^ 59
def prefixEnd_2695776 : Nat := 4983230072969 + 3 ^ 40 * 2695776 * 2
def baseEnd_2695776 : Nat := 307606405523322221711635

theorem tailTrace_2695776 : CollatzResearch.WordTrace tailWord_2695776 prefixEnd_2695776 307606405523322221711635 := by
  unfold tailWord_2695776
  simp only [CollatzResearch.WordTrace]
  refine ⟨49161514140835714365721591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65548685521114285820962121 49161514140835714365721591)
  ·
    refine ⟨73742271211253571548582387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49161514140835714365721591 73742271211253571548582387)
    ·
      refine ⟨110613406816880357322873581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73742271211253571548582387 110613406816880357322873581)
      ·
        refine ⟨41480027556330133996077593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110613406816880357322873581 41480027556330133996077593)
        ·
          refine ⟨31110020667247600497058195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41480027556330133996077593 31110020667247600497058195)
          ·
            refine ⟨46665031000871400745587293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31110020667247600497058195 46665031000871400745587293)
            ·
              refine ⟨17499386625326775279595235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46665031000871400745587293 17499386625326775279595235)
              ·
                refine ⟨26249079937990162919392853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17499386625326775279595235 26249079937990162919392853)
                ·
                  refine ⟨307606405523322221711635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26249079937990162919392853 307606405523322221711635)
                  ·
                    rfl

theorem cell22_2695776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 8].length) (baseStart_2695776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695776 prefixEnd_2695776 := by exact prefixLift 2695776
  have htrace : WordTrace (prefixWord ++ tailWord_2695776) baseStart_2695776 baseEnd_2695776 := by
    simpa [prefixWord, tailWord_2695776, baseEnd_2695776] using wordTrace_append hprefix tailTrace_2695776
  have hstable : (prefixWord ++ tailWord_2695776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695776).length < 2 ^ (prefixWord ++ tailWord_2695776).sum := by decide
  have hdescent : baseEnd_2695776 < baseStart_2695776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695857 : List Nat := [1, 2, 2, 6, 1, 1, 1, 2, 2, 4]
def baseStart_2695857 : Nat := 118140960795 + 2695857 * 2 ^ 59
def prefixEnd_2695857 : Nat := 4983230072969 + 3 ^ 40 * 2695857 * 2
def baseEnd_2695857 : Nat := 922846944525309453859657

theorem tailTrace_2695857 : CollatzResearch.WordTrace tailWord_2695857 prefixEnd_2695857 922846944525309453859657 := by
  unfold tailWord_2695857
  simp only [CollatzResearch.WordTrace]
  refine ⟨98325982594377979565141825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65550655062918653043427883 98325982594377979565141825)
  ·
    refine ⟨73744486945783484673856369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98325982594377979565141825 73744486945783484673856369)
    ·
      refine ⟨55308365209337613505392277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73744486945783484673856369 55308365209337613505392277)
      ·
        refine ⟨2592579619187700633065263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55308365209337613505392277 2592579619187700633065263)
        ·
          refine ⟨3888869428781550949597895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2592579619187700633065263 3888869428781550949597895)
          ·
            refine ⟨5833304143172326424396843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3888869428781550949597895 5833304143172326424396843)
            ·
              refine ⟨8749956214758489636595265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5833304143172326424396843 8749956214758489636595265)
              ·
                refine ⟨6562467161068867227446449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8749956214758489636595265 6562467161068867227446449)
                ·
                  refine ⟨4921850370801650420584837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6562467161068867227446449 4921850370801650420584837)
                  ·
                    refine ⟨922846944525309453859657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4921850370801650420584837 922846944525309453859657)
                    ·
                      rfl

theorem cell22_2695857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_2695857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695857 prefixEnd_2695857 := by exact prefixLift 2695857
  have htrace : WordTrace (prefixWord ++ tailWord_2695857) baseStart_2695857 baseEnd_2695857 := by
    simpa [prefixWord, tailWord_2695857, baseEnd_2695857] using wordTrace_append hprefix tailTrace_2695857
  have hstable : (prefixWord ++ tailWord_2695857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695857).length < 2 ^ (prefixWord ++ tailWord_2695857).sum := by decide
  have hdescent : baseEnd_2695857 < baseStart_2695857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695868 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 2, 6]
def baseStart_2695868 : Nat := 118140960795 + 2695868 * 2 ^ 59
def prefixEnd_2695868 : Nat := 4983230072969 + 3 ^ 40 * 2695868 * 2
def baseEnd_2695868 : Nat := 922850710050109091834623

theorem tailTrace_2695868 : CollatzResearch.WordTrace tailWord_2695868 prefixEnd_2695868 922850710050109091834623 := by
  unfold tailWord_2695868
  simp only [CollatzResearch.WordTrace]
  refine ⟨49163191898669064221896129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65550922531558752295861505 49163191898669064221896129)
  ·
    refine ⟨36872393924001798166422097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49163191898669064221896129 36872393924001798166422097)
    ·
      refine ⟨27654295443001348624816573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36872393924001798166422097 27654295443001348624816573)
      ·
        refine ⟨10370360791125505734306215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27654295443001348624816573 10370360791125505734306215)
        ·
          refine ⟨15555541186688258601459323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10370360791125505734306215 15555541186688258601459323)
          ·
            refine ⟨23333311780032387902188985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15555541186688258601459323 23333311780032387902188985)
            ·
              refine ⟨17499983835024290926641739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23333311780032387902188985 17499983835024290926641739)
              ·
                refine ⟨26249975752536436389962609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17499983835024290926641739 26249975752536436389962609)
                ·
                  refine ⟨19687481814402327292471957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26249975752536436389962609 19687481814402327292471957)
                  ·
                    refine ⟨922850710050109091834623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19687481814402327292471957 922850710050109091834623)
                    ·
                      rfl

theorem cell22_2695868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_2695868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695868 prefixEnd_2695868 := by exact prefixLift 2695868
  have htrace : WordTrace (prefixWord ++ tailWord_2695868) baseStart_2695868 baseEnd_2695868 := by
    simpa [prefixWord, tailWord_2695868, baseEnd_2695868] using wordTrace_append hprefix tailTrace_2695868
  have hstable : (prefixWord ++ tailWord_2695868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695868).length < 2 ^ (prefixWord ++ tailWord_2695868).sum := by decide
  have hdescent : baseEnd_2695868 < baseStart_2695868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695928 : List Nat := [2, 1, 2, 1, 1, 2, 4, 3, 6]
def baseStart_2695928 : Nat := 118140960795 + 2695928 * 2 ^ 59
def prefixEnd_2695928 : Nat := 4983230072969 + 3 ^ 40 * 2695928 * 2
def baseEnd_2695928 : Nat := 307623749758762978444813

theorem tailTrace_2695928 : CollatzResearch.WordTrace tailWord_2695928 prefixEnd_2695928 307623749758762978444813 := by
  unfold tailWord_2695928
  simp only [CollatzResearch.WordTrace]
  refine ⟨49164286088560379345488219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65552381451413839127317625 49164286088560379345488219)
  ·
    refine ⟨73746429132840569018232329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49164286088560379345488219 73746429132840569018232329)
    ·
      refine ⟨55309821849630426763674247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73746429132840569018232329 55309821849630426763674247)
      ·
        refine ⟨82964732774445640145511371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55309821849630426763674247 82964732774445640145511371)
        ·
          refine ⟨124447099161668460218267057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82964732774445640145511371 124447099161668460218267057)
          ·
            refine ⟨93335324371251345163700293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124447099161668460218267057 93335324371251345163700293)
            ·
              refine ⟨17500373319609627218193805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93335324371251345163700293 17500373319609627218193805)
              ·
                refine ⟨6562639994853610206822677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17500373319609627218193805 6562639994853610206822677)
                ·
                  refine ⟨307623749758762978444813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6562639994853610206822677 307623749758762978444813)
                  ·
                    rfl

theorem cell22_2695928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 6].length) (baseStart_2695928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695928 prefixEnd_2695928 := by exact prefixLift 2695928
  have htrace : WordTrace (prefixWord ++ tailWord_2695928) baseStart_2695928 baseEnd_2695928 := by
    simpa [prefixWord, tailWord_2695928, baseEnd_2695928] using wordTrace_append hprefix tailTrace_2695928
  have hstable : (prefixWord ++ tailWord_2695928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695928).length < 2 ^ (prefixWord ++ tailWord_2695928).sum := by decide
  have hdescent : baseEnd_2695928 < baseStart_2695928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695960 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 4, 3]
def baseStart_2695960 : Nat := 118140960795 + 2695960 * 2 ^ 59
def prefixEnd_2695960 : Nat := 4983230072969 + 3 ^ 40 * 2695960 * 2
def baseEnd_2695960 : Nat := 922882203530251518534341

theorem tailTrace_2695960 : CollatzResearch.WordTrace tailWord_2695960 prefixEnd_2695960 922882203530251518534341 := by
  unfold tailWord_2695960
  simp only [CollatzResearch.WordTrace]
  refine ⟨49164869656502414078070667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65553159542003218770760889 49164869656502414078070667)
  ·
    refine ⟨73747304484753621117106001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49164869656502414078070667 73747304484753621117106001)
    ·
      refine ⟨55310478363565215837829501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73747304484753621117106001 55310478363565215837829501)
      ·
        refine ⟨20741429386336955939186063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55310478363565215837829501 20741429386336955939186063)
        ·
          refine ⟨31112144079505433908779095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20741429386336955939186063 31112144079505433908779095)
          ·
            refine ⟨46668216119258150863168643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31112144079505433908779095 46668216119258150863168643)
            ·
              refine ⟨70002324178887226294752965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46668216119258150863168643 70002324178887226294752965)
              ·
                refine ⟨13125435783541354930266181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70002324178887226294752965 13125435783541354930266181)
                ·
                  refine ⟨2461019209414004049424909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13125435783541354930266181 2461019209414004049424909)
                  ·
                    refine ⟨922882203530251518534341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2461019209414004049424909 922882203530251518534341)
                    ·
                      rfl

theorem cell22_2695960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_2695960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695960 prefixEnd_2695960 := by exact prefixLift 2695960
  have htrace : WordTrace (prefixWord ++ tailWord_2695960) baseStart_2695960 baseEnd_2695960 := by
    simpa [prefixWord, tailWord_2695960, baseEnd_2695960] using wordTrace_append hprefix tailTrace_2695960
  have hstable : (prefixWord ++ tailWord_2695960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695960).length < 2 ^ (prefixWord ++ tailWord_2695960).sum := by decide
  have hdescent : baseEnd_2695960 < baseStart_2695960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695962 : List Nat := [3, 1, 1, 3, 2, 1, 4, 3, 4]
def baseStart_2695962 : Nat := 118140960795 + 2695962 * 2 ^ 59
def prefixEnd_2695962 : Nat := 4983230072969 + 3 ^ 40 * 2695962 * 2
def baseEnd_2695962 : Nat := 307627629390374726661445

theorem tailTrace_2695962 : CollatzResearch.WordTrace tailWord_2695962 prefixEnd_2695962 307627629390374726661445 := by
  unfold tailWord_2695962
  simp only [CollatzResearch.WordTrace]
  refine ⟨24582453064749395624428535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65553208172665054998476093 24582453064749395624428535)
  ·
    refine ⟨36873679597124093436642803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24582453064749395624428535 36873679597124093436642803)
    ·
      refine ⟨55310519395686140154964205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36873679597124093436642803 55310519395686140154964205)
      ·
        refine ⟨20741444773382302558111577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55310519395686140154964205 20741444773382302558111577)
        ·
          refine ⟨15556083580036726918583683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20741444773382302558111577 15556083580036726918583683)
          ·
            refine ⟨23334125370055090377875525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15556083580036726918583683 23334125370055090377875525)
            ·
              refine ⟨4375148506885329445851661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23334125370055090377875525 4375148506885329445851661)
              ·
                refine ⟨1640680690081998542194373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4375148506885329445851661 1640680690081998542194373)
                ·
                  refine ⟨307627629390374726661445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1640680690081998542194373 307627629390374726661445)
                  ·
                    rfl

theorem cell22_2695962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_2695962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695962 prefixEnd_2695962 := by exact prefixLift 2695962
  have htrace : WordTrace (prefixWord ++ tailWord_2695962) baseStart_2695962 baseEnd_2695962 := by
    simpa [prefixWord, tailWord_2695962, baseEnd_2695962] using wordTrace_append hprefix tailTrace_2695962
  have hstable : (prefixWord ++ tailWord_2695962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695962).length < 2 ^ (prefixWord ++ tailWord_2695962).sum := by decide
  have hdescent : baseEnd_2695962 < baseStart_2695962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695964 : List Nat := [2, 2, 3, 1, 1, 5, 2, 1, 1, 4]
def baseStart_2695964 : Nat := 118140960795 + 2695964 * 2 ^ 59
def prefixEnd_2695964 : Nat := 4983230072969 + 3 ^ 40 * 2695964 * 2
def baseEnd_2695964 : Nat := 922883572811996841434329

theorem tailTrace_2695964 : CollatzResearch.WordTrace tailWord_2695964 prefixEnd_2695964 922883572811996841434329 := by
  unfold tailWord_2695964
  simp only [CollatzResearch.WordTrace]
  refine ⟨49164942602495168419643473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65553256803326891226191297 49164942602495168419643473)
  ·
    refine ⟨36873706951871376314732605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49164942602495168419643473 36873706951871376314732605)
    ·
      refine ⟨13827640106951766118024727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36873706951871376314732605 13827640106951766118024727)
      ·
        refine ⟨20741460160427649177037091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13827640106951766118024727 20741460160427649177037091)
        ·
          refine ⟨31112190240641473765555637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20741460160427649177037091 31112190240641473765555637)
          ·
            refine ⟨2916767835060138165520841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31112190240641473765555637 2916767835060138165520841)
            ·
              refine ⟨2187575876295103624140631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2916767835060138165520841 2187575876295103624140631)
              ·
                refine ⟨3281363814442655436210947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2187575876295103624140631 3281363814442655436210947)
                ·
                  refine ⟨4922045721663983154316421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3281363814442655436210947 4922045721663983154316421)
                  ·
                    refine ⟨922883572811996841434329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4922045721663983154316421 922883572811996841434329)
                    ·
                      rfl

theorem cell22_2695964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_2695964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695964 prefixEnd_2695964 := by exact prefixLift 2695964
  have htrace : WordTrace (prefixWord ++ tailWord_2695964) baseStart_2695964 baseEnd_2695964 := by
    simpa [prefixWord, tailWord_2695964, baseEnd_2695964] using wordTrace_append hprefix tailTrace_2695964
  have hstable : (prefixWord ++ tailWord_2695964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695964).length < 2 ^ (prefixWord ++ tailWord_2695964).sum := by decide
  have hdescent : baseEnd_2695964 < baseStart_2695964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695973 : List Nat := [1, 3, 1, 2, 3, 1, 11]
def baseStart_2695973 : Nat := 118140960795 + 2695973 * 2 ^ 59
def prefixEnd_2695973 : Nat := 4983230072969 + 3 ^ 40 * 2695973 * 2
def baseEnd_2695973 : Nat := 34180987173923104368863

theorem tailTrace_2695973 : CollatzResearch.WordTrace tailWord_2695973 prefixEnd_2695973 34180987173923104368863 := by
  unfold tailWord_2695973
  simp only [CollatzResearch.WordTrace]
  refine ⟨98330213461957731376364573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65553475641305154250909715 98330213461957731376364573)
  ·
    refine ⟨36873830048234149266136715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98330213461957731376364573 36873830048234149266136715)
    ·
      refine ⟨55310745072351223899205073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36873830048234149266136715 55310745072351223899205073)
      ·
        refine ⟨41483058804263417924403805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55310745072351223899205073 41483058804263417924403805)
        ·
          refine ⟨15556147051598781721651427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41483058804263417924403805 15556147051598781721651427)
          ·
            refine ⟨23334220577398172582477141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15556147051598781721651427 23334220577398172582477141)
            ·
              refine ⟨34180987173923104368863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23334220577398172582477141 34180987173923104368863)
              ·
                rfl

theorem cell22_2695973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 11].length) (baseStart_2695973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695973 prefixEnd_2695973 := by exact prefixLift 2695973
  have htrace : WordTrace (prefixWord ++ tailWord_2695973) baseStart_2695973 baseEnd_2695973 := by
    simpa [prefixWord, tailWord_2695973, baseEnd_2695973] using wordTrace_append hprefix tailTrace_2695973
  have hstable : (prefixWord ++ tailWord_2695973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695973).length < 2 ^ (prefixWord ++ tailWord_2695973).sum := by decide
  have hdescent : baseEnd_2695973 < baseStart_2695973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695994 : List Nat := [3, 1, 1, 1, 7, 1, 1, 1, 1, 5]
def baseStart_2695994 : Nat := 118140960795 + 2695994 * 2 ^ 59
def prefixEnd_2695994 : Nat := 4983230072969 + 3 ^ 40 * 2695994 * 2
def baseEnd_2695994 : Nat := 922893842425086763184237

theorem tailTrace_2695994 : CollatzResearch.WordTrace tailWord_2695994 prefixEnd_2695994 922893842425086763184237 := by
  unfold tailWord_2695994
  simp only [CollatzResearch.WordTrace]
  refine ⟨24582744848720412990719759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65553986263254434641919357 24582744848720412990719759)
  ·
    refine ⟨36874117273080619486079639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24582744848720412990719759 36874117273080619486079639)
    ·
      refine ⟨55311175909620929229119459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36874117273080619486079639 55311175909620929229119459)
      ·
        refine ⟨82966763864431393843679189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55311175909620929229119459 82966763864431393843679189)
        ·
          refine ⟨1944533528072610793211231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 82966763864431393843679189 1944533528072610793211231)
          ·
            refine ⟨2916800292108916189816847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944533528072610793211231 2916800292108916189816847)
            ·
              refine ⟨4375200438163374284725271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2916800292108916189816847 4375200438163374284725271)
              ·
                refine ⟨6562800657245061427087907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4375200438163374284725271 6562800657245061427087907)
                ·
                  refine ⟨9844200985867592140631861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6562800657245061427087907 9844200985867592140631861)
                  ·
                    refine ⟨922893842425086763184237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9844200985867592140631861 922893842425086763184237)
                    ·
                      rfl

theorem cell22_2695994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 1, 5].length) (baseStart_2695994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2695994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2695994 prefixEnd_2695994 := by exact prefixLift 2695994
  have htrace : WordTrace (prefixWord ++ tailWord_2695994) baseStart_2695994 baseEnd_2695994 := by
    simpa [prefixWord, tailWord_2695994, baseEnd_2695994] using wordTrace_append hprefix tailTrace_2695994
  have hstable : (prefixWord ++ tailWord_2695994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695994).length < 2 ^ (prefixWord ++ tailWord_2695994).sum := by decide
  have hdescent : baseEnd_2695994 < baseStart_2695994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696005 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 5, 3]
def baseStart_2696005 : Nat := 118140960795 + 2696005 * 2 ^ 59
def prefixEnd_2696005 : Nat := 4983230072969 + 3 ^ 40 * 2696005 * 2
def baseEnd_2696005 : Nat := 922897607949886401159203

theorem tailTrace_2696005 : CollatzResearch.WordTrace tailWord_2696005 prefixEnd_2696005 922897607949886401159203 := by
  unfold tailWord_2696005
  simp only [CollatzResearch.WordTrace]
  refine ⟨98331380597841800841529469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65554253731894533894352979 98331380597841800841529469)
  ·
    refine ⟨36874267724190675315573551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98331380597841800841529469 36874267724190675315573551)
    ·
      refine ⟨55311401586286012973360327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36874267724190675315573551 55311401586286012973360327)
      ·
        refine ⟨82967102379429019460040491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55311401586286012973360327 82967102379429019460040491)
        ·
          refine ⟨124450653569143529190060737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82967102379429019460040491 124450653569143529190060737)
          ·
            refine ⟨93337990176857646892545553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124450653569143529190060737 93337990176857646892545553)
            ·
              refine ⟨70003492632643235169409165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93337990176857646892545553 70003492632643235169409165)
              ·
                refine ⟨26251309737241213188528437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70003492632643235169409165 26251309737241213188528437)
                ·
                  refine ⟨2461060287866363736424541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26251309737241213188528437 2461060287866363736424541)
                  ·
                    refine ⟨922897607949886401159203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2461060287866363736424541 922897607949886401159203)
                    ·
                      rfl

theorem cell22_2696005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_2696005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696005 prefixEnd_2696005 := by exact prefixLift 2696005
  have htrace : WordTrace (prefixWord ++ tailWord_2696005) baseStart_2696005 baseEnd_2696005 := by
    simpa [prefixWord, tailWord_2696005, baseEnd_2696005] using wordTrace_append hprefix tailTrace_2696005
  have hstable : (prefixWord ++ tailWord_2696005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696005).length < 2 ^ (prefixWord ++ tailWord_2696005).sum := by decide
  have hdescent : baseEnd_2696005 < baseStart_2696005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696013 : List Nat := [1, 6, 1, 2, 3, 1, 1, 3, 4]
def baseStart_2696013 : Nat := 118140960795 + 2696013 * 2 ^ 59
def prefixEnd_2696013 : Nat := 4983230072969 + 3 ^ 40 * 2696013 * 2
def baseEnd_2696013 : Nat := 307633448837792348986393

theorem tailTrace_2696013 : CollatzResearch.WordTrace tailWord_2696013 prefixEnd_2696013 307633448837792348986393 := by
  unfold tailWord_2696013
  simp only [CollatzResearch.WordTrace]
  refine ⟨98331672381812818207820693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65554448254541878805213795 98331672381812818207820693)
  ·
    refine ⟨4609297142897475853491595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 98331672381812818207820693 4609297142897475853491595)
    ·
      refine ⟨6913945714346213780237393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4609297142897475853491595 6913945714346213780237393)
      ·
        refine ⟨5185459285759660335178045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6913945714346213780237393 5185459285759660335178045)
        ·
          refine ⟨1944547232159872625691767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5185459285759660335178045 1944547232159872625691767)
          ·
            refine ⟨2916820848239808938537651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944547232159872625691767 2916820848239808938537651)
            ·
              refine ⟨4375231272359713407806477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2916820848239808938537651 4375231272359713407806477)
              ·
                refine ⟨1640711727134892527927429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4375231272359713407806477 1640711727134892527927429)
                ·
                  refine ⟨307633448837792348986393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1640711727134892527927429 307633448837792348986393)
                  ·
                    rfl

theorem cell22_2696013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_2696013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696013 prefixEnd_2696013 := by exact prefixLift 2696013
  have htrace : WordTrace (prefixWord ++ tailWord_2696013) baseStart_2696013 baseEnd_2696013 := by
    simpa [prefixWord, tailWord_2696013, baseEnd_2696013] using wordTrace_append hprefix tailTrace_2696013
  have hstable : (prefixWord ++ tailWord_2696013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696013).length < 2 ^ (prefixWord ++ tailWord_2696013).sum := by decide
  have hdescent : baseEnd_2696013 < baseStart_2696013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696035 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 7]
def baseStart_2696035 : Nat := 118140960795 + 2696035 * 2 ^ 59
def prefixEnd_2696035 : Nat := 4983230072969 + 3 ^ 40 * 2696035 * 2
def baseEnd_2696035 : Nat := 307635959187658774303037

theorem tailTrace_2696035 : CollatzResearch.WordTrace tailWord_2696035 prefixEnd_2696035 307635959187658774303037 := by
  unfold tailWord_2696035
  simp only [CollatzResearch.WordTrace]
  refine ⟨98332474787733115965121559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65554983191822077310081039 98332474787733115965121559)
  ·
    refine ⟨147498712181599673947682339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98332474787733115965121559 147498712181599673947682339)
    ·
      refine ⟨221248068272399510921523509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147498712181599673947682339 221248068272399510921523509)
      ·
        refine ⟨20742006400537454148892829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 221248068272399510921523509 20742006400537454148892829)
        ·
          refine ⟨7778252400201545305834811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20742006400537454148892829 7778252400201545305834811)
          ·
            refine ⟨11667378600302317958752217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7778252400201545305834811 11667378600302317958752217)
            ·
              refine ⟨8750533950226738469064163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11667378600302317958752217 8750533950226738469064163)
              ·
                refine ⟨13125800925340107703596245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8750533950226738469064163 13125800925340107703596245)
                ·
                  refine ⟨307635959187658774303037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13125800925340107703596245 307635959187658774303037)
                  ·
                    rfl

theorem cell22_2696035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 7].length) (baseStart_2696035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696035 prefixEnd_2696035 := by exact prefixLift 2696035
  have htrace : WordTrace (prefixWord ++ tailWord_2696035) baseStart_2696035 baseEnd_2696035 := by
    simpa [prefixWord, tailWord_2696035, baseEnd_2696035] using wordTrace_append hprefix tailTrace_2696035
  have hstable : (prefixWord ++ tailWord_2696035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696035).length < 2 ^ (prefixWord ++ tailWord_2696035).sum := by decide
  have hdescent : baseEnd_2696035 < baseStart_2696035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696039 : List Nat := [1, 1, 5, 1, 2, 4, 1, 1, 3, 3]
def baseStart_2696039 : Nat := 118140960795 + 2696039 * 2 ^ 59
def prefixEnd_2696039 : Nat := 4983230072969 + 3 ^ 40 * 2696039 * 2
def baseEnd_2696039 : Nat := 922909246844721645809099

theorem tailTrace_2696039 : CollatzResearch.WordTrace tailWord_2696039 prefixEnd_2696039 922909246844721645809099 := by
  unfold tailWord_2696039
  simp only [CollatzResearch.WordTrace]
  refine ⟨98332620679718624648267171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65555080453145749765511447 98332620679718624648267171)
  ·
    refine ⟨147498931019577936972400757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98332620679718624648267171 147498931019577936972400757)
    ·
      refine ⟨13828024783085431591162571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147498931019577936972400757 13828024783085431591162571)
      ·
        refine ⟨20742037174628147386743857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13828024783085431591162571 20742037174628147386743857)
        ·
          refine ⟨15556527880971110540057893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20742037174628147386743857 15556527880971110540057893)
          ·
            refine ⟨2916848977682083226260855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15556527880971110540057893 2916848977682083226260855)
            ·
              refine ⟨4375273466523124839391283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2916848977682083226260855 4375273466523124839391283)
              ·
                refine ⟨6562910199784687259086925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4375273466523124839391283 6562910199784687259086925)
                ·
                  refine ⟨2461091324919257722157597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6562910199784687259086925 2461091324919257722157597)
                  ·
                    refine ⟨922909246844721645809099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2461091324919257722157597 922909246844721645809099)
                    ·
                      rfl

theorem cell22_2696039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_2696039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696039 prefixEnd_2696039 := by exact prefixLift 2696039
  have htrace : WordTrace (prefixWord ++ tailWord_2696039) baseStart_2696039 baseEnd_2696039 := by
    simpa [prefixWord, tailWord_2696039, baseEnd_2696039] using wordTrace_append hprefix tailTrace_2696039
  have hstable : (prefixWord ++ tailWord_2696039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696039).length < 2 ^ (prefixWord ++ tailWord_2696039).sum := by decide
  have hdescent : baseEnd_2696039 < baseStart_2696039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696050 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_2696050 : Nat := 118140960795 + 2696050 * 2 ^ 59
def prefixEnd_2696050 : Nat := 4983230072969 + 3 ^ 40 * 2696050 * 2
def baseEnd_2696050 : Nat := 922913012369521283784065

theorem tailTrace_2696050 : CollatzResearch.WordTrace tailWord_2696050 prefixEnd_2696050 922913012369521283784065 := by
  unfold tailWord_2696050
  simp only [CollatzResearch.WordTrace]
  refine ⟨24583255470669693381729401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65555347921785849017945069 24583255470669693381729401)
  ·
    refine ⟨18437441603002270036297051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24583255470669693381729401 18437441603002270036297051)
    ·
      refine ⟨27656162404503405054445577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18437441603002270036297051 27656162404503405054445577)
      ·
        refine ⟨20742121803377553790834183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27656162404503405054445577 20742121803377553790834183)
        ·
          refine ⟨31113182705066330686251275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20742121803377553790834183 31113182705066330686251275)
          ·
            refine ⟨46669774057599496029376913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31113182705066330686251275 46669774057599496029376913)
            ·
              refine ⟨35002330543199622022032685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46669774057599496029376913 35002330543199622022032685)
              ·
                refine ⟨13125873953699858258262257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35002330543199622022032685 13125873953699858258262257)
                ·
                  refine ⟨9844405465274893693696693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13125873953699858258262257 9844405465274893693696693)
                  ·
                    refine ⟨922913012369521283784065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9844405465274893693696693 922913012369521283784065)
                    ·
                      rfl

theorem cell22_2696050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_2696050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696050 prefixEnd_2696050 := by exact prefixLift 2696050
  have htrace : WordTrace (prefixWord ++ tailWord_2696050) baseStart_2696050 baseEnd_2696050 := by
    simpa [prefixWord, tailWord_2696050, baseEnd_2696050] using wordTrace_append hprefix tailTrace_2696050
  have hstable : (prefixWord ++ tailWord_2696050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696050).length < 2 ^ (prefixWord ++ tailWord_2696050).sum := by decide
  have hdescent : baseEnd_2696050 < baseStart_2696050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696086 : List Nat := [5, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2696086 : Nat := 118140960795 + 2696086 * 2 ^ 59
def prefixEnd_2696086 : Nat := 4983230072969 + 3 ^ 40 * 2696086 * 2
def baseEnd_2696086 : Nat := 307641778635076396627985

theorem tailTrace_2696086 : CollatzResearch.WordTrace tailWord_2696086 prefixEnd_2696086 307641778635076396627985 := by
  unfold tailWord_2696086
  simp only [CollatzResearch.WordTrace]
  refine ⟨6145895931909271979701757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65556223273698901116818741 6145895931909271979701757)
  ·
    refine ⟨2304710974465976992388159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6145895931909271979701757 2304710974465976992388159)
    ·
      refine ⟨3457066461698965488582239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2304710974465976992388159 3457066461698965488582239)
      ·
        refine ⟨5185599692548448232873359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3457066461698965488582239 5185599692548448232873359)
        ·
          refine ⟨7778399538822672349310039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5185599692548448232873359 7778399538822672349310039)
          ·
            refine ⟨11667599308234008523965059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7778399538822672349310039 11667599308234008523965059)
            ·
              refine ⟨17501398962351012785947589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11667599308234008523965059 17501398962351012785947589)
              ·
                refine ⟨3281512305440814897365173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17501398962351012785947589 3281512305440814897365173)
                ·
                  refine ⟨307641778635076396627985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3281512305440814897365173 307641778635076396627985)
                  ·
                    rfl

theorem cell22_2696086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2696086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696086 prefixEnd_2696086 := by exact prefixLift 2696086
  have htrace : WordTrace (prefixWord ++ tailWord_2696086) baseStart_2696086 baseEnd_2696086 := by
    simpa [prefixWord, tailWord_2696086, baseEnd_2696086] using wordTrace_append hprefix tailTrace_2696086
  have hstable : (prefixWord ++ tailWord_2696086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696086).length < 2 ^ (prefixWord ++ tailWord_2696086).sum := by decide
  have hdescent : baseEnd_2696086 < baseStart_2696086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696090 : List Nat := [3, 1, 1, 4, 4, 1, 2, 2, 1, 3]
def baseStart_2696090 : Nat := 118140960795 + 2696090 * 2 ^ 59
def prefixEnd_2696090 : Nat := 4983230072969 + 3 ^ 40 * 2696090 * 2
def baseEnd_2696090 : Nat := 922926705186974512783943

theorem tailTrace_2696090 : CollatzResearch.WordTrace tailWord_2696090 prefixEnd_2696090 922926705186974512783943 := by
  unfold tailWord_2696090
  simp only [CollatzResearch.WordTrace]
  refine ⟨24583620200633465089593431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65556320535022573572249149 24583620200633465089593431)
  ·
    refine ⟨36875430300950197634390147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24583620200633465089593431 36875430300950197634390147)
    ·
      refine ⟨55313145451425296451585221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36875430300950197634390147 55313145451425296451585221)
      ·
        refine ⟨10371214772142243084672229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55313145451425296451585221 10371214772142243084672229)
        ·
          refine ⟨1944602769776670578376043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10371214772142243084672229 1944602769776670578376043)
          ·
            refine ⟨2916904154665005867564065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944602769776670578376043 2916904154665005867564065)
            ·
              refine ⟨2187678115998754400673049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2916904154665005867564065 2187678115998754400673049)
              ·
                refine ⟨1640758586999065800504787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2187678115998754400673049 1640758586999065800504787)
                ·
                  refine ⟨2461137880498598700757181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640758586999065800504787 2461137880498598700757181)
                  ·
                    refine ⟨922926705186974512783943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2461137880498598700757181 922926705186974512783943)
                    ·
                      rfl

theorem cell22_2696090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 1, 3].length) (baseStart_2696090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696090 prefixEnd_2696090 := by exact prefixLift 2696090
  have htrace : WordTrace (prefixWord ++ tailWord_2696090) baseStart_2696090 baseEnd_2696090 := by
    simpa [prefixWord, tailWord_2696090, baseEnd_2696090] using wordTrace_append hprefix tailTrace_2696090
  have hstable : (prefixWord ++ tailWord_2696090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696090).length < 2 ^ (prefixWord ++ tailWord_2696090).sum := by decide
  have hdescent : baseEnd_2696090 < baseStart_2696090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696146 : List Nat := [3, 2, 2, 3, 1, 1, 3, 2, 2, 3]
def baseStart_2696146 : Nat := 118140960795 + 2696146 * 2 ^ 59
def prefixEnd_2696146 : Nat := 4983230072969 + 3 ^ 40 * 2696146 * 2
def baseEnd_2696146 : Nat := 922945875131409033383771

theorem tailTrace_2696146 : CollatzResearch.WordTrace tailWord_2696146 prefixEnd_2696146 922945875131409033383771 := by
  unfold tailWord_2696146
  simp only [CollatzResearch.WordTrace]
  refine ⟨24584130822582745480603073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65557682193553987948274861 24584130822582745480603073)
  ·
    refine ⟨18438098116937059110452305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24584130822582745480603073 18438098116937059110452305)
    ·
      refine ⟨13828573587702794332839229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18438098116937059110452305 13828573587702794332839229)
      ·
        refine ⟨5185715095388547874814711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13828573587702794332839229 5185715095388547874814711)
        ·
          refine ⟨7778572643082821812222067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5185715095388547874814711 7778572643082821812222067)
          ·
            refine ⟨11667858964624232718333101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7778572643082821812222067 11667858964624232718333101)
            ·
              refine ⟨4375447111734087269374913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11667858964624232718333101 4375447111734087269374913)
              ·
                refine ⟨3281585333800565452031185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4375447111734087269374913 3281585333800565452031185)
                ·
                  refine ⟨2461189000350424089023389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3281585333800565452031185 2461189000350424089023389)
                  ·
                    refine ⟨922945875131409033383771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2461189000350424089023389 922945875131409033383771)
                    ·
                      rfl

theorem cell22_2696146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_2696146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696146 prefixEnd_2696146 := by exact prefixLift 2696146
  have htrace : WordTrace (prefixWord ++ tailWord_2696146) baseStart_2696146 baseEnd_2696146 := by
    simpa [prefixWord, tailWord_2696146, baseEnd_2696146] using wordTrace_append hprefix tailTrace_2696146
  have hstable : (prefixWord ++ tailWord_2696146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696146).length < 2 ^ (prefixWord ++ tailWord_2696146).sum := by decide
  have hdescent : baseEnd_2696146 < baseStart_2696146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696266 : List Nat := [3, 1, 2, 1, 1, 2, 6, 2, 4]
def baseStart_2696266 : Nat := 118140960795 + 2696266 * 2 ^ 59
def prefixEnd_2696266 : Nat := 4983230072969 + 3 ^ 40 * 2696266 * 2
def baseEnd_2696266 : Nat := 307662317861256240127801

theorem tailTrace_2696266 : CollatzResearch.WordTrace tailWord_2696266 prefixEnd_2696266 307662317861256240127801 := by
  unfold tailWord_2696266
  simp only [CollatzResearch.WordTrace]
  refine ⟨24585225012474060604195163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65560600033264161611187101 24585225012474060604195163)
  ·
    refine ⟨36877837518711090906292745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24585225012474060604195163 36877837518711090906292745)
    ·
      refine ⟨27658378139033318179719559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36877837518711090906292745 27658378139033318179719559)
      ·
        refine ⟨41487567208549977269579339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27658378139033318179719559 41487567208549977269579339)
        ·
          refine ⟨62231350812824965904369009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41487567208549977269579339 62231350812824965904369009)
          ·
            refine ⟨46673513109618724428276757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62231350812824965904369009 46673513109618724428276757)
            ·
              refine ⟨2187820927013377707575473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46673513109618724428276757 2187820927013377707575473)
              ·
                refine ⟨1640865695260033280681605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2187820927013377707575473 1640865695260033280681605)
                ·
                  refine ⟨307662317861256240127801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1640865695260033280681605 307662317861256240127801)
                  ·
                    rfl

theorem cell22_2696266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_2696266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696266 prefixEnd_2696266 := by exact prefixLift 2696266
  have htrace : WordTrace (prefixWord ++ tailWord_2696266) baseStart_2696266 baseEnd_2696266 := by
    simpa [prefixWord, tailWord_2696266, baseEnd_2696266] using wordTrace_append hprefix tailTrace_2696266
  have hstable : (prefixWord ++ tailWord_2696266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696266).length < 2 ^ (prefixWord ++ tailWord_2696266).sum := by decide
  have hdescent : baseEnd_2696266 < baseStart_2696266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696296 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 1, 6]
def baseStart_2696296 : Nat := 118140960795 + 2696296 * 2 ^ 59
def prefixEnd_2696296 : Nat := 4983230072969 + 3 ^ 40 * 2696296 * 2
def baseEnd_2696296 : Nat := 922997223196858642133311

theorem tailTrace_2696296 : CollatzResearch.WordTrace tailWord_2696296 prefixEnd_2696296 922997223196858642133311 := by
  unfold tailWord_2696296
  simp only [CollatzResearch.WordTrace]
  refine ⟨49170997119893778770186371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65561329493191705026915161 49170997119893778770186371)
  ·
    refine ⟨73756495679840668155279557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49170997119893778770186371 73756495679840668155279557)
    ·
      refine ⟨13829342939970125279114917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73756495679840668155279557 13829342939970125279114917)
      ·
        refine ⟨2593001801244398489834047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13829342939970125279114917 2593001801244398489834047)
        ·
          refine ⟨3889502701866597734751071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2593001801244398489834047 3889502701866597734751071)
          ·
            refine ⟨5834254052799896602126607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3889502701866597734751071 5834254052799896602126607)
            ·
              refine ⟨8751381079199844903189911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5834254052799896602126607 8751381079199844903189911)
              ·
                refine ⟨13127071618799767354784867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8751381079199844903189911 13127071618799767354784867)
                ·
                  refine ⟨19690607428199651032177301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13127071618799767354784867 19690607428199651032177301)
                  ·
                    refine ⟨922997223196858642133311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19690607428199651032177301 922997223196858642133311)
                    ·
                      rfl

theorem cell22_2696296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_2696296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696296 prefixEnd_2696296 := by exact prefixLift 2696296
  have htrace : WordTrace (prefixWord ++ tailWord_2696296) baseStart_2696296 baseEnd_2696296 := by
    simpa [prefixWord, tailWord_2696296, baseEnd_2696296] using wordTrace_append hprefix tailTrace_2696296
  have hstable : (prefixWord ++ tailWord_2696296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696296).length < 2 ^ (prefixWord ++ tailWord_2696296).sum := by decide
  have hdescent : baseEnd_2696296 < baseStart_2696296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696367 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 8]
def baseStart_2696367 : Nat := 118140960795 + 2696367 * 2 ^ 59
def prefixEnd_2696367 : Nat := 4983230072969 + 3 ^ 40 * 2696367 * 2
def baseEnd_2696367 : Nat := 307673842649279374536031

theorem tailTrace_2696367 : CollatzResearch.WordTrace tailWord_2696367 prefixEnd_2696367 307673842649279374536031 := by
  unfold tailWord_2696367
  simp only [CollatzResearch.WordTrace]
  refine ⟨98344583822530336666207355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65563055881686891110804903 98344583822530336666207355)
  ·
    refine ⟨147516875733795504999311033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98344583822530336666207355 147516875733795504999311033)
    ·
      refine ⟨110637656800346628749483275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147516875733795504999311033 110637656800346628749483275)
      ·
        refine ⟨165956485200519943124224913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110637656800346628749483275 165956485200519943124224913)
        ·
          refine ⟨124467363900389957343168685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165956485200519943124224913 124467363900389957343168685)
          ·
            refine ⟨46675261462646234003688257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124467363900389957343168685 46675261462646234003688257)
            ·
              refine ⟨35006446096984675502766193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46675261462646234003688257 35006446096984675502766193)
              ·
                refine ⟨26254834572738506627074645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35006446096984675502766193 26254834572738506627074645)
                ·
                  refine ⟨307673842649279374536031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26254834572738506627074645 307673842649279374536031)
                  ·
                    rfl

theorem cell22_2696367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 8].length) (baseStart_2696367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696367 prefixEnd_2696367 := by exact prefixLift 2696367
  have htrace : WordTrace (prefixWord ++ tailWord_2696367) baseStart_2696367 baseEnd_2696367 := by
    simpa [prefixWord, tailWord_2696367, baseEnd_2696367] using wordTrace_append hprefix tailTrace_2696367
  have hstable : (prefixWord ++ tailWord_2696367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696367).length < 2 ^ (prefixWord ++ tailWord_2696367).sum := by decide
  have hdescent : baseEnd_2696367 < baseStart_2696367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696399 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 6, 3]
def baseStart_2696399 : Nat := 118140960795 + 2696399 * 2 ^ 59
def prefixEnd_2696399 : Nat := 4983230072969 + 3 ^ 40 * 2696399 * 2
def baseEnd_2696399 : Nat := 923032482201800706807995

theorem tailTrace_2696399 : CollatzResearch.WordTrace tailWord_2696399 prefixEnd_2696399 923032482201800706807995 := by
  unfold tailWord_2696399
  simp only [CollatzResearch.WordTrace]
  refine ⟨98345750958414406131372251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65563833972276270754248167 98345750958414406131372251)
  ·
    refine ⟨147518626437621609197058377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98345750958414406131372251 147518626437621609197058377)
    ·
      refine ⟨110638969828216206897793783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147518626437621609197058377 110638969828216206897793783)
      ·
        refine ⟨165958454742324310346690675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110638969828216206897793783 165958454742324310346690675)
        ·
          refine ⟨248937682113486465520036013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165958454742324310346690675 248937682113486465520036013)
          ·
            refine ⟨93351630792557424570013505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248937682113486465520036013 93351630792557424570013505)
            ·
              refine ⟨70013723094418068427510129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93351630792557424570013505 70013723094418068427510129)
              ·
                refine ⟨52510292320813551320632597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70013723094418068427510129 52510292320813551320632597)
                ·
                  refine ⟨2461419952538135218154653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52510292320813551320632597 2461419952538135218154653)
                  ·
                    refine ⟨923032482201800706807995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2461419952538135218154653 923032482201800706807995)
                    ·
                      rfl

theorem cell22_2696399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 3].length) (baseStart_2696399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696399 prefixEnd_2696399 := by exact prefixLift 2696399
  have htrace : WordTrace (prefixWord ++ tailWord_2696399) baseStart_2696399 baseEnd_2696399 := by
    simpa [prefixWord, tailWord_2696399, baseEnd_2696399] using wordTrace_append hprefix tailTrace_2696399
  have hstable : (prefixWord ++ tailWord_2696399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696399).length < 2 ^ (prefixWord ++ tailWord_2696399).sum := by decide
  have hdescent : baseEnd_2696399 < baseStart_2696399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696429 : List Nat := [1, 5, 1, 2, 2, 11]
def baseStart_2696429 : Nat := 118140960795 + 2696429 * 2 ^ 59
def prefixEnd_2696429 : Nat := 4983230072969 + 3 ^ 40 * 2696429 * 2
def baseEnd_2696429 : Nat := 11395589528578896648863

theorem tailTrace_2696429 : CollatzResearch.WordTrace tailWord_2696429 prefixEnd_2696429 11395589528578896648863 := by
  unfold tailWord_2696429
  simp only [CollatzResearch.WordTrace]
  refine ⟨98346845148305721254964341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65564563432203814169976227 98346845148305721254964341)
  ·
    refine ⟨9220016732653661367652907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98346845148305721254964341 9220016732653661367652907)
    ·
      refine ⟨13830025098980492051479361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9220016732653661367652907 13830025098980492051479361)
      ·
        refine ⟨10372518824235369038609521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13830025098980492051479361 10372518824235369038609521)
        ·
          refine ⟨7779389118176526778957141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10372518824235369038609521 7779389118176526778957141)
          ·
            refine ⟨11395589528578896648863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7779389118176526778957141 11395589528578896648863)
            ·
              rfl

theorem cell22_2696429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 11].length) (baseStart_2696429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696429 prefixEnd_2696429 := by exact prefixLift 2696429
  have htrace : WordTrace (prefixWord ++ tailWord_2696429) baseStart_2696429 baseEnd_2696429 := by
    simpa [prefixWord, tailWord_2696429, baseEnd_2696429] using wordTrace_append hprefix tailTrace_2696429
  have hstable : (prefixWord ++ tailWord_2696429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696429).length < 2 ^ (prefixWord ++ tailWord_2696429).sum := by decide
  have hdescent : baseEnd_2696429 < baseStart_2696429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696446 : List Nat := [4, 2, 2, 1, 1, 2, 3, 7]
def baseStart_2696446 : Nat := 118140960795 + 2696446 * 2 ^ 59
def prefixEnd_2696446 : Nat := 4983230072969 + 3 ^ 40 * 2696446 * 2
def baseEnd_2696446 : Nat := 102560952362478694542539

theorem tailTrace_2696446 : CollatzResearch.WordTrace tailWord_2696446 prefixEnd_2696446 102560952362478694542539 := by
  unfold tailWord_2696446
  simp only [CollatzResearch.WordTrace]
  refine ⟨12293433148655516644791649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65564976792829422105555461 12293433148655516644791649)
  ·
    refine ⟨9220074861491637483593737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12293433148655516644791649 9220074861491637483593737)
    ·
      refine ⟨6915056146118728112695303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9220074861491637483593737 6915056146118728112695303)
      ·
        refine ⟨10372584219178092169042955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6915056146118728112695303 10372584219178092169042955)
        ·
          refine ⟨15558876328767138253564433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10372584219178092169042955 15558876328767138253564433)
          ·
            refine ⟨11669157246575353690173325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15558876328767138253564433 11669157246575353690173325)
            ·
              refine ⟨4375933967465757633814997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11669157246575353690173325 4375933967465757633814997)
              ·
                refine ⟨102560952362478694542539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4375933967465757633814997 102560952362478694542539)
                ·
                  rfl

theorem cell22_2696446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_2696446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696446 prefixEnd_2696446 := by exact prefixLift 2696446
  have htrace : WordTrace (prefixWord ++ tailWord_2696446) baseStart_2696446 baseEnd_2696446 := by
    simpa [prefixWord, tailWord_2696446, baseEnd_2696446] using wordTrace_append hprefix tailTrace_2696446
  have hstable : (prefixWord ++ tailWord_2696446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696446).length < 2 ^ (prefixWord ++ tailWord_2696446).sum := by decide
  have hdescent : baseEnd_2696446 < baseStart_2696446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696508 : List Nat := [2, 2, 2, 2, 1, 4, 3, 1, 5]
def baseStart_2696508 : Nat := 118140960795 + 2696508 * 2 ^ 59
def prefixEnd_2696508 : Nat := 4983230072969 + 3 ^ 40 * 2696508 * 2
def baseEnd_2696508 : Nat := 307689931709786918610887

theorem tailTrace_2696508 : CollatzResearch.WordTrace tailWord_2696508 prefixEnd_2696508 307689931709786918610887 := by
  unfold tailWord_2696508
  simp only [CollatzResearch.WordTrace]
  refine ⟨49174863257509758873545089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65566484343346345164726785 49174863257509758873545089)
  ·
    refine ⟨36881147443132319155158817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49174863257509758873545089 36881147443132319155158817)
    ·
      refine ⟨27660860582349239366369113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36881147443132319155158817 27660860582349239366369113)
      ·
        refine ⟨20745645436761929524776835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27660860582349239366369113 20745645436761929524776835)
        ·
          refine ⟨31118468155142894287165253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20745645436761929524776835 31118468155142894287165253)
          ·
            refine ⟨5834712779089292678843485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31118468155142894287165253 5834712779089292678843485)
            ·
              refine ⟨2188017292158484754566307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5834712779089292678843485 2188017292158484754566307)
              ·
                refine ⟨3282025938237727131849461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2188017292158484754566307 3282025938237727131849461)
                ·
                  refine ⟨307689931709786918610887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3282025938237727131849461 307689931709786918610887)
                  ·
                    rfl

theorem cell22_2696508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_2696508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696508 prefixEnd_2696508 := by exact prefixLift 2696508
  have htrace : WordTrace (prefixWord ++ tailWord_2696508) baseStart_2696508 baseEnd_2696508 := by
    simpa [prefixWord, tailWord_2696508, baseEnd_2696508] using wordTrace_append hprefix tailTrace_2696508
  have hstable : (prefixWord ++ tailWord_2696508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696508).length < 2 ^ (prefixWord ++ tailWord_2696508).sum := by decide
  have hdescent : baseEnd_2696508 < baseStart_2696508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696521 : List Nat := [1, 2, 1, 1, 2, 3, 3, 4, 1, 4]
def baseStart_2696521 : Nat := 118140960795 + 2696521 * 2 ^ 59
def prefixEnd_2696521 : Nat := 4983230072969 + 3 ^ 40 * 2696521 * 2
def baseEnd_2696521 : Nat := 923074245295033055257621

theorem tailTrace_2696521 : CollatzResearch.WordTrace tailWord_2696521 prefixEnd_2696521 923074245295033055257621 := by
  unfold tailWord_2696521
  simp only [CollatzResearch.WordTrace]
  refine ⟨98350200663972420967313417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65566800442648280644875611 98350200663972420967313417)
  ·
    refine ⟨73762650497979315725485063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98350200663972420967313417 73762650497979315725485063)
    ·
      refine ⟨110643975746968973588227595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73762650497979315725485063 110643975746968973588227595)
      ·
        refine ⟨165965963620453460382341393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110643975746968973588227595 165965963620453460382341393)
        ·
          refine ⟨124474472715340095286756045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165965963620453460382341393 124474472715340095286756045)
          ·
            refine ⟨46677927268252535732533517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124474472715340095286756045 46677927268252535732533517)
            ·
              refine ⟨17504222725594700899700069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46677927268252535732533517 17504222725594700899700069)
              ·
                refine ⟨3282041761049006418693763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17504222725594700899700069 3282041761049006418693763)
                ·
                  refine ⟨4923062641573509628040645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3282041761049006418693763 4923062641573509628040645)
                  ·
                    refine ⟨923074245295033055257621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4923062641573509628040645 923074245295033055257621)
                    ·
                      rfl

theorem cell22_2696521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 4].length) (baseStart_2696521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696521 prefixEnd_2696521 := by exact prefixLift 2696521
  have htrace : WordTrace (prefixWord ++ tailWord_2696521) baseStart_2696521 baseEnd_2696521 := by
    simpa [prefixWord, tailWord_2696521, baseEnd_2696521] using wordTrace_append hprefix tailTrace_2696521
  have hstable : (prefixWord ++ tailWord_2696521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696521).length < 2 ^ (prefixWord ++ tailWord_2696521).sum := by decide
  have hdescent : baseEnd_2696521 < baseStart_2696521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696583 : List Nat := [1, 1, 4, 2, 2, 3, 2, 1, 2, 4]
def baseStart_2696583 : Nat := 118140960795 + 2696583 * 2 ^ 59
def prefixEnd_2696583 : Nat := 4983230072969 + 3 ^ 40 * 2696583 * 2
def baseEnd_2696583 : Nat := 923095469162085560207431

theorem tailTrace_2696583 : CollatzResearch.WordTrace tailWord_2696583 prefixEnd_2696583 923095469162085560207431 := by
  unfold tailWord_2696583
  simp only [CollatzResearch.WordTrace]
  refine ⟨98352461989747805556070403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65568307993165203704046935 98352461989747805556070403)
  ·
    refine ⟨147528692984621708334105605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98352461989747805556070403 147528692984621708334105605)
    ·
      refine ⟨27661629934616570312644801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147528692984621708334105605 27661629934616570312644801)
      ·
        refine ⟨20746222450962427734483601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27661629934616570312644801 20746222450962427734483601)
        ·
          refine ⟨15559666838221820800862701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20746222450962427734483601 15559666838221820800862701)
          ·
            refine ⟨5834875064333182800323513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15559666838221820800862701 5834875064333182800323513)
            ·
              refine ⟨4376156298249887100242635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5834875064333182800323513 4376156298249887100242635)
              ·
                refine ⟨6564234447374830650363953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4376156298249887100242635 6564234447374830650363953)
                ·
                  refine ⟨4923175835531122987772965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6564234447374830650363953 4923175835531122987772965)
                  ·
                    refine ⟨923095469162085560207431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4923175835531122987772965 923095469162085560207431)
                    ·
                      rfl

theorem cell22_2696583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_2696583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696583 prefixEnd_2696583 := by exact prefixLift 2696583
  have htrace : WordTrace (prefixWord ++ tailWord_2696583) baseStart_2696583 baseEnd_2696583 := by
    simpa [prefixWord, tailWord_2696583, baseEnd_2696583] using wordTrace_append hprefix tailTrace_2696583
  have hstable : (prefixWord ++ tailWord_2696583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696583).length < 2 ^ (prefixWord ++ tailWord_2696583).sum := by decide
  have hdescent : baseEnd_2696583 < baseStart_2696583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696598 : List Nat := [5, 3, 1, 13]
def baseStart_2696598 : Nat := 118140960795 + 2696598 * 2 ^ 59
def prefixEnd_2696598 : Nat := 4983230072969 + 3 ^ 40 * 2696598 * 2
def baseEnd_2696598 : Nat := 1266255972522126915065

theorem tailTrace_2696598 : CollatzResearch.WordTrace tailWord_2696598 prefixEnd_2696598 1266255972522126915065 := by
  unfold tailWord_2696598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6147063067793341444866653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65568672723128975411910965 6147063067793341444866653)
  ·
    refine ⟨2305148650422503041824995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6147063067793341444866653 2305148650422503041824995)
    ·
      refine ⟨3457722975633754562737493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2305148650422503041824995 3457722975633754562737493)
      ·
        refine ⟨1266255972522126915065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3457722975633754562737493 1266255972522126915065)
        ·
          rfl

theorem cell22_2696598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 13].length) (baseStart_2696598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696598 prefixEnd_2696598 := by exact prefixLift 2696598
  have htrace : WordTrace (prefixWord ++ tailWord_2696598) baseStart_2696598 baseEnd_2696598 := by
    simpa [prefixWord, tailWord_2696598, baseEnd_2696598] using wordTrace_append hprefix tailTrace_2696598
  have hstable : (prefixWord ++ tailWord_2696598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696598).length < 2 ^ (prefixWord ++ tailWord_2696598).sum := by decide
  have hdescent : baseEnd_2696598 < baseStart_2696598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696604 : List Nat := [2, 2, 3, 4, 1, 2, 2, 2, 4]
def baseStart_2696604 : Nat := 118140960795 + 2696604 * 2 ^ 59
def prefixEnd_2696604 : Nat := 4983230072969 + 3 ^ 40 * 2696604 * 2
def baseEnd_2696604 : Nat := 307700885963749501810789

theorem tailTrace_2696604 : CollatzResearch.WordTrace tailWord_2696604 prefixEnd_2696604 307700885963749501810789 := by
  unfold tailWord_2696604
  simp only [CollatzResearch.WordTrace]
  refine ⟨49176613961335863071292433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65568818615114484095056577 49176613961335863071292433)
  ·
    refine ⟨36882460471001897303469325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49176613961335863071292433 36882460471001897303469325)
    ·
      refine ⟨13830922676625711488800997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36882460471001897303469325 13830922676625711488800997)
      ·
        refine ⟨2593298001867320904150187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13830922676625711488800997 2593298001867320904150187)
        ·
          refine ⟨3889947002800981356225281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2593298001867320904150187 3889947002800981356225281)
          ·
            refine ⟨2917460252100736017168961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3889947002800981356225281 2917460252100736017168961)
            ·
              refine ⟨2188095189075552012876721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2917460252100736017168961 2188095189075552012876721)
              ·
                refine ⟨1641071391806664009657541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2188095189075552012876721 1641071391806664009657541)
                ·
                  refine ⟨307700885963749501810789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1641071391806664009657541 307700885963749501810789)
                  ·
                    rfl

theorem cell22_2696604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_2696604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696604 prefixEnd_2696604 := by exact prefixLift 2696604
  have htrace : WordTrace (prefixWord ++ tailWord_2696604) baseStart_2696604 baseEnd_2696604 := by
    simpa [prefixWord, tailWord_2696604, baseEnd_2696604] using wordTrace_append hprefix tailTrace_2696604
  have hstable : (prefixWord ++ tailWord_2696604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696604).length < 2 ^ (prefixWord ++ tailWord_2696604).sum := by decide
  have hdescent : baseEnd_2696604 < baseStart_2696604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696690 : List Nat := [3, 2, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_2696690 : Nat := 118140960795 + 2696690 * 2 ^ 59
def prefixEnd_2696690 : Nat := 4983230072969 + 3 ^ 40 * 2696690 * 2
def baseEnd_2696690 : Nat := 923132097448772947782103

theorem tailTrace_2696690 : CollatzResearch.WordTrace tailWord_2696690 prefixEnd_2696690 923132097448772947782103 := by
  unfold tailWord_2696690
  simp only [CollatzResearch.WordTrace]
  refine ⟨24589091150090040707553881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65570909733573441886810349 24589091150090040707553881)
  ·
    refine ⟨18441818362567530530665411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24589091150090040707553881 18441818362567530530665411)
    ·
      refine ⟨27662727543851295795998117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18441818362567530530665411 27662727543851295795998117)
      ·
        refine ⟨5186761414472117961749647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27662727543851295795998117 5186761414472117961749647)
        ·
          refine ⟨7780142121708176942624471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5186761414472117961749647 7780142121708176942624471)
          ·
            refine ⟨11670213182562265413936707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7780142121708176942624471 11670213182562265413936707)
            ·
              refine ⟨17505319773843398120905061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11670213182562265413936707 17505319773843398120905061)
              ·
                refine ⟨3282247457595637147669699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17505319773843398120905061 3282247457595637147669699)
                ·
                  refine ⟨4923371186393455721504549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3282247457595637147669699 4923371186393455721504549)
                  ·
                    refine ⟨923132097448772947782103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4923371186393455721504549 923132097448772947782103)
                    ·
                      rfl

theorem cell22_2696690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_2696690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696690 prefixEnd_2696690 := by exact prefixLift 2696690
  have htrace : WordTrace (prefixWord ++ tailWord_2696690) baseStart_2696690 baseEnd_2696690 := by
    simpa [prefixWord, tailWord_2696690, baseEnd_2696690] using wordTrace_append hprefix tailTrace_2696690
  have hstable : (prefixWord ++ tailWord_2696690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696690).length < 2 ^ (prefixWord ++ tailWord_2696690).sum := by decide
  have hdescent : baseEnd_2696690 < baseStart_2696690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696733 : List Nat := [1, 4, 2, 2, 1, 1, 4, 7]
def baseStart_2696733 : Nat := 118140960795 + 2696733 * 2 ^ 59
def prefixEnd_2696733 : Nat := 4983230072969 + 3 ^ 40 * 2696733 * 2
def baseEnd_2696733 : Nat := 102571868580837240995219

theorem tailTrace_2696733 : CollatzResearch.WordTrace tailWord_2696733 prefixEnd_2696733 102571868580837240995219 := by
  unfold tailWord_2696733
  simp only [CollatzResearch.WordTrace]
  refine ⟨98357932939204381174030853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65571955292802920782687235 98357932939204381174030853)
  ·
    refine ⟨18442112426100821470130785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98357932939204381174030853 18442112426100821470130785)
    ·
      refine ⟨13831584319575616102598089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18442112426100821470130785 13831584319575616102598089)
      ·
        refine ⟨10373688239681712076948567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13831584319575616102598089 10373688239681712076948567)
        ·
          refine ⟨15560532359522568115422851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10373688239681712076948567 15560532359522568115422851)
          ·
            refine ⟨23340798539283852173134277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15560532359522568115422851 23340798539283852173134277)
            ·
              refine ⟨4376399726115722282462677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23340798539283852173134277 4376399726115722282462677)
              ·
                refine ⟨102571868580837240995219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4376399726115722282462677 102571868580837240995219)
                ·
                  rfl

theorem cell22_2696733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 7].length) (baseStart_2696733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696733 prefixEnd_2696733 := by exact prefixLift 2696733
  have htrace : WordTrace (prefixWord ++ tailWord_2696733) baseStart_2696733 baseEnd_2696733 := by
    simpa [prefixWord, tailWord_2696733, baseEnd_2696733] using wordTrace_append hprefix tailTrace_2696733
  have hstable : (prefixWord ++ tailWord_2696733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696733).length < 2 ^ (prefixWord ++ tailWord_2696733).sum := by decide
  have hdescent : baseEnd_2696733 < baseStart_2696733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696737 : List Nat := [1, 2, 3, 2, 2, 2, 4, 1, 2, 3]
def baseStart_2696737 : Nat := 118140960795 + 2696737 * 2 ^ 59
def prefixEnd_2696737 : Nat := 4983230072969 + 3 ^ 40 * 2696737 * 2
def baseEnd_2696737 : Nat := 923148186509280491856959

theorem tailTrace_2696737 : CollatzResearch.WordTrace tailWord_2696737 prefixEnd_2696737 923148186509280491856959 := by
  unfold tailWord_2696737
  simp only [CollatzResearch.WordTrace]
  refine ⟨98358078831189889857176465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65572052554126593238117643 98358078831189889857176465)
  ·
    refine ⟨73768559123392417392882349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98358078831189889857176465 73768559123392417392882349)
    ·
      refine ⟨27663209671272156522330881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73768559123392417392882349 27663209671272156522330881)
      ·
        refine ⟨20747407253454117391748161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27663209671272156522330881 20747407253454117391748161)
        ·
          refine ⟨15560555440090588043811121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20747407253454117391748161 15560555440090588043811121)
          ·
            refine ⟨11670416580067941032858341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15560555440090588043811121 11670416580067941032858341)
            ·
              refine ⟨2188203108762738943660939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11670416580067941032858341 2188203108762738943660939)
              ·
                refine ⟨3282304663144108415491409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2188203108762738943660939 3282304663144108415491409)
                ·
                  refine ⟨2461728497358081311618557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3282304663144108415491409 2461728497358081311618557)
                  ·
                    refine ⟨923148186509280491856959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2461728497358081311618557 923148186509280491856959)
                    ·
                      rfl

theorem cell22_2696737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_2696737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696737 prefixEnd_2696737 := by exact prefixLift 2696737
  have htrace : WordTrace (prefixWord ++ tailWord_2696737) baseStart_2696737 baseEnd_2696737 := by
    simpa [prefixWord, tailWord_2696737, baseEnd_2696737] using wordTrace_append hprefix tailTrace_2696737
  have hstable : (prefixWord ++ tailWord_2696737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696737).length < 2 ^ (prefixWord ++ tailWord_2696737).sum := by decide
  have hdescent : baseEnd_2696737 < baseStart_2696737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696825 : List Nat := [1, 2, 1, 3, 3, 1, 3, 3, 1, 4]
def baseStart_2696825 : Nat := 118140960795 + 2696825 * 2 ^ 59
def prefixEnd_2696825 : Nat := 4983230072969 + 3 ^ 40 * 2696825 * 2
def baseEnd_2696825 : Nat := 923178310707677595656689

theorem tailTrace_2696825 : CollatzResearch.WordTrace tailWord_2696825 prefixEnd_2696825 923178310707677595656689 := by
  unfold tailWord_2696825
  simp only [CollatzResearch.WordTrace]
  refine ⟨98361288454871080886379929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65574192303247387257586619 98361288454871080886379929)
  ·
    refine ⟨73770966341153310664784947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98361288454871080886379929 73770966341153310664784947)
    ·
      refine ⟨110656449511729965997177421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73770966341153310664784947 110656449511729965997177421)
      ·
        refine ⟨41496168566898737248941533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110656449511729965997177421 41496168566898737248941533)
        ·
          refine ⟨15561063212587026468353075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41496168566898737248941533 15561063212587026468353075)
          ·
            refine ⟨23341594818880539702529613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15561063212587026468353075 23341594818880539702529613)
            ·
              refine ⟨8753098057080202388448605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23341594818880539702529613 8753098057080202388448605)
              ·
                refine ⟨3282411771405075895668227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8753098057080202388448605 3282411771405075895668227)
                ·
                  refine ⟨4923617657107613843502341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3282411771405075895668227 4923617657107613843502341)
                  ·
                    refine ⟨923178310707677595656689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4923617657107613843502341 923178310707677595656689)
                    ·
                      rfl

theorem cell22_2696825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 4].length) (baseStart_2696825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696825 prefixEnd_2696825 := by exact prefixLift 2696825
  have htrace : WordTrace (prefixWord ++ tailWord_2696825) baseStart_2696825 baseEnd_2696825 := by
    simpa [prefixWord, tailWord_2696825, baseEnd_2696825] using wordTrace_append hprefix tailTrace_2696825
  have hstable : (prefixWord ++ tailWord_2696825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696825).length < 2 ^ (prefixWord ++ tailWord_2696825).sum := by decide
  have hdescent : baseEnd_2696825 < baseStart_2696825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696855 : List Nat := [1, 1, 3, 3, 2, 2, 3, 1, 1, 5]
def baseStart_2696855 : Nat := 118140960795 + 2696855 * 2 ^ 59
def prefixEnd_2696855 : Nat := 4983230072969 + 3 ^ 40 * 2696855 * 2
def baseEnd_2696855 : Nat := 923188580320767517406597

theorem tailTrace_2696855 : CollatzResearch.WordTrace tailWord_2696855 prefixEnd_2696855 923188580320767517406597 := by
  unfold tailWord_2696855
  simp only [CollatzResearch.WordTrace]
  refine ⟨98362382644762396009972019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65574921763174930673314679 98362382644762396009972019)
  ·
    refine ⟨147543573967143594014958029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98362382644762396009972019 147543573967143594014958029)
    ·
      refine ⟨55328840237678847755609261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147543573967143594014958029 55328840237678847755609261)
      ·
        refine ⟨20748315089129567908353473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55328840237678847755609261 20748315089129567908353473)
        ·
          refine ⟨15561236316847175931265105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20748315089129567908353473 15561236316847175931265105)
          ·
            refine ⟨11670927237635381948448829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15561236316847175931265105 11670927237635381948448829)
            ·
              refine ⟨4376597714113268230668311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11670927237635381948448829 4376597714113268230668311)
              ·
                refine ⟨6564896571169902346002467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4376597714113268230668311 6564896571169902346002467)
                ·
                  refine ⟨9847344856754853519003701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6564896571169902346002467 9847344856754853519003701)
                  ·
                    refine ⟨923188580320767517406597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9847344856754853519003701 923188580320767517406597)
                    ·
                      rfl

theorem cell22_2696855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_2696855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696855 prefixEnd_2696855 := by exact prefixLift 2696855
  have htrace : WordTrace (prefixWord ++ tailWord_2696855) baseStart_2696855 baseEnd_2696855 := by
    simpa [prefixWord, tailWord_2696855, baseEnd_2696855] using wordTrace_append hprefix tailTrace_2696855
  have hstable : (prefixWord ++ tailWord_2696855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696855).length < 2 ^ (prefixWord ++ tailWord_2696855).sum := by decide
  have hdescent : baseEnd_2696855 < baseStart_2696855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696906 : List Nat := [3, 1, 2, 1, 5, 2, 2, 1, 2, 3]
def baseStart_2696906 : Nat := 118140960795 + 2696906 * 2 ^ 59
def prefixEnd_2696906 : Nat := 4983230072969 + 3 ^ 40 * 2696906 * 2
def baseEnd_2696906 : Nat := 923206038663020384381441

theorem tailTrace_2696906 : CollatzResearch.WordTrace tailWord_2696906 prefixEnd_2696906 923206038663020384381441 := by
  unfold tailWord_2696906
  simp only [CollatzResearch.WordTrace]
  refine ⟨24591060691894407930019643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65576161845051754480052381 24591060691894407930019643)
  ·
    refine ⟨36886591037841611895029465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24591060691894407930019643 36886591037841611895029465)
    ·
      refine ⟨27664943278381208921272099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36886591037841611895029465 27664943278381208921272099)
      ·
        refine ⟨41497414917571813381908149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27664943278381208921272099 41497414917571813381908149)
        ·
          refine ⟨3890382648522357504553889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41497414917571813381908149 3890382648522357504553889)
          ·
            refine ⟨2917786986391768128415417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3890382648522357504553889 2917786986391768128415417)
            ·
              refine ⟨2188340239793826096311563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2917786986391768128415417 2188340239793826096311563)
              ·
                refine ⟨3282510359690739144467345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2188340239793826096311563 3282510359690739144467345)
                ·
                  refine ⟨2461882769768054358350509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3282510359690739144467345 2461882769768054358350509)
                  ·
                    refine ⟨923206038663020384381441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2461882769768054358350509 923206038663020384381441)
                    ·
                      rfl

theorem cell22_2696906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_2696906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696906 prefixEnd_2696906 := by exact prefixLift 2696906
  have htrace : WordTrace (prefixWord ++ tailWord_2696906) baseStart_2696906 baseEnd_2696906 := by
    simpa [prefixWord, tailWord_2696906, baseEnd_2696906] using wordTrace_append hprefix tailTrace_2696906
  have hstable : (prefixWord ++ tailWord_2696906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696906).length < 2 ^ (prefixWord ++ tailWord_2696906).sum := by decide
  have hdescent : baseEnd_2696906 < baseStart_2696906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696962 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_2696962 : Nat := 118140960795 + 2696962 * 2 ^ 59
def prefixEnd_2696962 : Nat := 4983230072969 + 3 ^ 40 * 2696962 * 2
def baseEnd_2696962 : Nat := 923225208607454904981269

theorem tailTrace_2696962 : CollatzResearch.WordTrace tailWord_2696962 prefixEnd_2696962 923225208607454904981269 := by
  unfold tailWord_2696962
  simp only [CollatzResearch.WordTrace]
  refine ⟨24591571313843688321029285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65577523503583168856078093 24591571313843688321029285)
  ·
    refine ⟨4610919621345691560192991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24591571313843688321029285 4610919621345691560192991)
    ·
      refine ⟨6916379432018537340289487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4610919621345691560192991 6916379432018537340289487)
      ·
        refine ⟨10374569148027806010434231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6916379432018537340289487 10374569148027806010434231)
        ·
          refine ⟨15561853722041709015651347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10374569148027806010434231 15561853722041709015651347)
          ·
            refine ⟨23342780583062563523477021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15561853722041709015651347 23342780583062563523477021)
            ·
              refine ⟨8753542718648461321303883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23342780583062563523477021 8753542718648461321303883)
              ·
                refine ⟨13130314077972691981955825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8753542718648461321303883 13130314077972691981955825)
                ·
                  refine ⟨9847735558479518986466869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13130314077972691981955825 9847735558479518986466869)
                  ·
                    refine ⟨923225208607454904981269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9847735558479518986466869 923225208607454904981269)
                    ·
                      rfl

theorem cell22_2696962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_2696962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2696962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2696962 prefixEnd_2696962 := by exact prefixLift 2696962
  have htrace : WordTrace (prefixWord ++ tailWord_2696962) baseStart_2696962 baseEnd_2696962 := by
    simpa [prefixWord, tailWord_2696962, baseEnd_2696962] using wordTrace_append hprefix tailTrace_2696962
  have hstable : (prefixWord ++ tailWord_2696962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696962).length < 2 ^ (prefixWord ++ tailWord_2696962).sum := by decide
  have hdescent : baseEnd_2696962 < baseStart_2696962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697022 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_2697022 : Nat := 118140960795 + 2697022 * 2 ^ 59
def prefixEnd_2697022 : Nat := 4983230072969 + 3 ^ 40 * 2697022 * 2
def baseEnd_2697022 : Nat := 923245747833634748481085

theorem tailTrace_2697022 : CollatzResearch.WordTrace tailWord_2697022 prefixEnd_2697022 923245747833634748481085 := by
  unfold tailWord_2697022
  simp only [CollatzResearch.WordTrace]
  refine ⟨12296059204394672941412665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65578982423438255687534213 12296059204394672941412665)
  ·
    refine ⟨9222044403296004706059499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12296059204394672941412665 9222044403296004706059499)
    ·
      refine ⟨13833066604944007059089249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9222044403296004706059499 13833066604944007059089249)
      ·
        refine ⟨10374799953708005294316937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13833066604944007059089249 10374799953708005294316937)
        ·
          refine ⟨7781099965281003970737703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10374799953708005294316937 7781099965281003970737703)
          ·
            refine ⟨11671649947921505956106555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7781099965281003970737703 11671649947921505956106555)
            ·
              refine ⟨17507474921882258934159833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11671649947921505956106555 17507474921882258934159833)
              ·
                refine ⟨13130606191411694200619875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17507474921882258934159833 13130606191411694200619875)
                ·
                  refine ⟨19695909287117541300929813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13130606191411694200619875 19695909287117541300929813)
                  ·
                    refine ⟨923245747833634748481085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19695909287117541300929813 923245747833634748481085)
                    ·
                      rfl

theorem cell22_2697022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_2697022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697022 prefixEnd_2697022 := by exact prefixLift 2697022
  have htrace : WordTrace (prefixWord ++ tailWord_2697022) baseStart_2697022 baseEnd_2697022 := by
    simpa [prefixWord, tailWord_2697022, baseEnd_2697022] using wordTrace_append hprefix tailTrace_2697022
  have hstable : (prefixWord ++ tailWord_2697022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697022).length < 2 ^ (prefixWord ++ tailWord_2697022).sum := by decide
  have hdescent : baseEnd_2697022 < baseStart_2697022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697069 : List Nat := [1, 5, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_2697069 : Nat := 118140960795 + 2697069 * 2 ^ 59
def prefixEnd_2697069 : Nat := 4983230072969 + 3 ^ 40 * 2697069 * 2
def baseEnd_2697069 : Nat := 923261836894142292555941

theorem tailTrace_2697069 : CollatzResearch.WordTrace tailWord_2697069 prefixEnd_2697069 923261836894142292555941 := by
  unfold tailWord_2697069
  simp only [CollatzResearch.WordTrace]
  refine ⟨98370187865987110558262261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65580125243991407038841507 98370187865987110558262261)
  ·
    refine ⟨9222205112436291614837087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98370187865987110558262261 9222205112436291614837087)
    ·
      refine ⟨13833307668654437422255631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9222205112436291614837087 13833307668654437422255631)
      ·
        refine ⟨20749961502981656133383447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13833307668654437422255631 20749961502981656133383447)
        ·
          refine ⟨31124942254472484200075171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20749961502981656133383447 31124942254472484200075171)
          ·
            refine ⟨46687413381708726300112757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31124942254472484200075171 46687413381708726300112757)
            ·
              refine ⟨4376945004535193090635571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46687413381708726300112757 4376945004535193090635571)
              ·
                refine ⟨6565417506802789635953357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4376945004535193090635571 6565417506802789635953357)
                ·
                  refine ⟨2462031565051046113482509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6565417506802789635953357 2462031565051046113482509)
                  ·
                    refine ⟨923261836894142292555941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2462031565051046113482509 923261836894142292555941)
                    ·
                      rfl

theorem cell22_2697069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_2697069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697069 prefixEnd_2697069 := by exact prefixLift 2697069
  have htrace : WordTrace (prefixWord ++ tailWord_2697069) baseStart_2697069 baseEnd_2697069 := by
    simpa [prefixWord, tailWord_2697069, baseEnd_2697069] using wordTrace_append hprefix tailTrace_2697069
  have hstable : (prefixWord ++ tailWord_2697069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697069).length < 2 ^ (prefixWord ++ tailWord_2697069).sum := by decide
  have hdescent : baseEnd_2697069 < baseStart_2697069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697080 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 6, 5]
def baseStart_2697080 : Nat := 118140960795 + 2697080 * 2 ^ 59
def prefixEnd_2697080 : Nat := 4983230072969 + 3 ^ 40 * 2697080 * 2
def baseEnd_2697080 : Nat := 923265602418941930530907

theorem tailTrace_2697080 : CollatzResearch.WordTrace tailWord_2697080 prefixEnd_2697080 923265602418941930530907 := by
  unfold tailWord_2697080
  simp only [CollatzResearch.WordTrace]
  refine ⟨49185294534473629718456347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65580392712631506291275129 49185294534473629718456347)
  ·
    refine ⟨73777941801710444577684521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49185294534473629718456347 73777941801710444577684521)
    ·
      refine ⟨55333456351282833433263391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73777941801710444577684521 55333456351282833433263391)
      ·
        refine ⟨83000184526924250149895087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55333456351282833433263391 83000184526924250149895087)
        ·
          refine ⟨124500276790386375224842631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83000184526924250149895087 124500276790386375224842631)
          ·
            refine ⟨186750415185579562837263947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124500276790386375224842631 186750415185579562837263947)
            ·
              refine ⟨280125622778369344255895921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186750415185579562837263947 280125622778369344255895921)
              ·
                refine ⟨210094217083777008191921941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280125622778369344255895921 210094217083777008191921941)
                ·
                  refine ⟨9848166425802047258996341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 210094217083777008191921941 9848166425802047258996341)
                  ·
                    refine ⟨923265602418941930530907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9848166425802047258996341 923265602418941930530907)
                    ·
                      rfl

theorem cell22_2697080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_2697080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697080 prefixEnd_2697080 := by exact prefixLift 2697080
  have htrace : WordTrace (prefixWord ++ tailWord_2697080) baseStart_2697080 baseEnd_2697080 := by
    simpa [prefixWord, tailWord_2697080, baseEnd_2697080] using wordTrace_append hprefix tailTrace_2697080
  have hstable : (prefixWord ++ tailWord_2697080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697080).length < 2 ^ (prefixWord ++ tailWord_2697080).sum := by decide
  have hdescent : baseEnd_2697080 < baseStart_2697080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697157 : List Nat := [1, 3, 1, 1, 1, 1, 1, 7, 2, 4]
def baseStart_2697157 : Nat := 118140960795 + 2697157 * 2 ^ 59
def prefixEnd_2697157 : Nat := 4983230072969 + 3 ^ 40 * 2697157 * 2
def baseEnd_2697157 : Nat := 923291961092539396355671

theorem tailTrace_2697157 : CollatzResearch.WordTrace tailWord_2697157 prefixEnd_2697157 923291961092539396355671 := by
  unfold tailWord_2697157
  simp only [CollatzResearch.WordTrace]
  refine ⟨98373397489668301587465725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65582264993112201058310483 98373397489668301587465725)
  ·
    refine ⟨36890024058625613095299647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98373397489668301587465725 36890024058625613095299647)
    ·
      refine ⟨55335036087938419642949471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36890024058625613095299647 55335036087938419642949471)
      ·
        refine ⟨83002554131907629464424207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55335036087938419642949471 83002554131907629464424207)
        ·
          refine ⟨124503831197861444196636311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83002554131907629464424207 124503831197861444196636311)
          ·
            refine ⟨186755746796792166294954467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124503831197861444196636311 186755746796792166294954467)
            ·
              refine ⟨280133620195188249442431701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186755746796792166294954467 280133620195188249442431701)
              ·
                refine ⟨6565631723324724596306993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 280133620195188249442431701 6565631723324724596306993)
                ·
                  refine ⟨4924223792493543447230245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6565631723324724596306993 4924223792493543447230245)
                  ·
                    refine ⟨923291961092539396355671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4924223792493543447230245 923291961092539396355671)
                    ·
                      rfl

theorem cell22_2697157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_2697157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697157 prefixEnd_2697157 := by exact prefixLift 2697157
  have htrace : WordTrace (prefixWord ++ tailWord_2697157) baseStart_2697157 baseEnd_2697157 := by
    simpa [prefixWord, tailWord_2697157, baseEnd_2697157] using wordTrace_append hprefix tailTrace_2697157
  have hstable : (prefixWord ++ tailWord_2697157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697157).length < 2 ^ (prefixWord ++ tailWord_2697157).sum := by decide
  have hdescent : baseEnd_2697157 < baseStart_2697157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697172 : List Nat := [2, 4, 1, 2, 1, 1, 11]
def baseStart_2697172 : Nat := 118140960795 + 2697172 * 2 ^ 59
def prefixEnd_2697172 : Nat := 4983230072969 + 3 ^ 40 * 2697172 * 2
def baseEnd_2697172 : Nat := 34196188737003124341875

theorem tailTrace_2697172 : CollatzResearch.WordTrace tailWord_2697172 prefixEnd_2697172 34196188737003124341875 := by
  unfold tailWord_2697172
  simp only [CollatzResearch.WordTrace]
  refine ⟨49186972292306979574630885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65582629723075972766174513 49186972292306979574630885)
  ·
    refine ⟨9222557304807558670243291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49186972292306979574630885 9222557304807558670243291)
    ·
      refine ⟨13833835957211338005364937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9222557304807558670243291 13833835957211338005364937)
      ·
        refine ⟨10375376967908503504023703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13833835957211338005364937 10375376967908503504023703)
        ·
          refine ⟨15563065451862755256035555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10375376967908503504023703 15563065451862755256035555)
          ·
            refine ⟨23344598177794132884053333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15563065451862755256035555 23344598177794132884053333)
            ·
              refine ⟨34196188737003124341875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23344598177794132884053333 34196188737003124341875)
              ·
                rfl

theorem cell22_2697172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 11].length) (baseStart_2697172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697172 prefixEnd_2697172 := by exact prefixLift 2697172
  have htrace : WordTrace (prefixWord ++ tailWord_2697172) baseStart_2697172 baseEnd_2697172 := by
    simpa [prefixWord, tailWord_2697172, baseEnd_2697172] using wordTrace_append hprefix tailTrace_2697172
  have hstable : (prefixWord ++ tailWord_2697172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697172).length < 2 ^ (prefixWord ++ tailWord_2697172).sum := by decide
  have hdescent : baseEnd_2697172 < baseStart_2697172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697217 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 9]
def baseStart_2697217 : Nat := 118140960795 + 2697217 * 2 ^ 59
def prefixEnd_2697217 : Nat := 4983230072969 + 3 ^ 40 * 2697217 * 2
def baseEnd_2697217 : Nat := 307770833439573079951829

theorem tailTrace_2697217 : CollatzResearch.WordTrace tailWord_2697217 prefixEnd_2697217 307770833439573079951829 := by
  unfold tailWord_2697217
  simp only [CollatzResearch.WordTrace]
  refine ⟨98375585869450931834649905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65583723912967287889766603 98375585869450931834649905)
  ·
    refine ⟨73781689402088198875987429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98375585869450931834649905 73781689402088198875987429)
    ·
      refine ⟨13834066762891537289247643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73781689402088198875987429 13834066762891537289247643)
      ·
        refine ⟨20751100144337305933871465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13834066762891537289247643 20751100144337305933871465)
        ·
          refine ⟨15563325108252979450403599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20751100144337305933871465 15563325108252979450403599)
          ·
            refine ⟨23344987662379469175605399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15563325108252979450403599 23344987662379469175605399)
            ·
              refine ⟨35017481493569203763408099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23344987662379469175605399 35017481493569203763408099)
              ·
                refine ⟨52526222240353805645112149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35017481493569203763408099 52526222240353805645112149)
                ·
                  refine ⟨307770833439573079951829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52526222240353805645112149 307770833439573079951829)
                  ·
                    rfl

theorem cell22_2697217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 9].length) (baseStart_2697217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697217 prefixEnd_2697217 := by exact prefixLift 2697217
  have htrace : WordTrace (prefixWord ++ tailWord_2697217) baseStart_2697217 baseEnd_2697217 := by
    simpa [prefixWord, tailWord_2697217, baseEnd_2697217] using wordTrace_append hprefix tailTrace_2697217
  have hstable : (prefixWord ++ tailWord_2697217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697217).length < 2 ^ (prefixWord ++ tailWord_2697217).sum := by decide
  have hdescent : baseEnd_2697217 < baseStart_2697217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697264 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 3, 4]
def baseStart_2697264 : Nat := 118140960795 + 2697264 * 2 ^ 59
def prefixEnd_2697264 : Nat := 4983230072969 + 3 ^ 40 * 2697264 * 2
def baseEnd_2697264 : Nat := 923328589379226783930343

theorem tailTrace_2697264 : CollatzResearch.WordTrace tailWord_2697264 prefixEnd_2697264 923328589379226783930343 := by
  unfold tailWord_2697264
  simp only [CollatzResearch.WordTrace]
  refine ⟨49188650050140329430805423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65584866733520439241073897 49188650050140329430805423)
  ·
    refine ⟨73782975075210494146208135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49188650050140329430805423 73782975075210494146208135)
    ·
      refine ⟨110674462612815741219312203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73782975075210494146208135 110674462612815741219312203)
      ·
        refine ⟨166011693919223611828968305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110674462612815741219312203 166011693919223611828968305)
        ·
          refine ⟨124508770439417708871726229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166011693919223611828968305 124508770439417708871726229)
          ·
            refine ⟨5836348614347705103362167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124508770439417708871726229 5836348614347705103362167)
            ·
              refine ⟨8754522921521557655043251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5836348614347705103362167 8754522921521557655043251)
              ·
                refine ⟨13131784382282336482564877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8754522921521557655043251 13131784382282336482564877)
                ·
                  refine ⟨4924419143355876180961829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13131784382282336482564877 4924419143355876180961829)
                  ·
                    refine ⟨923328589379226783930343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4924419143355876180961829 923328589379226783930343)
                    ·
                      rfl

theorem cell22_2697264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_2697264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697264 prefixEnd_2697264 := by exact prefixLift 2697264
  have htrace : WordTrace (prefixWord ++ tailWord_2697264) baseStart_2697264 baseEnd_2697264 := by
    simpa [prefixWord, tailWord_2697264, baseEnd_2697264] using wordTrace_append hprefix tailTrace_2697264
  have hstable : (prefixWord ++ tailWord_2697264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697264).length < 2 ^ (prefixWord ++ tailWord_2697264).sum := by decide
  have hdescent : baseEnd_2697264 < baseStart_2697264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697345 : List Nat := [1, 2, 4, 2, 3, 2, 1, 2, 2, 3]
def baseStart_2697345 : Nat := 118140960795 + 2697345 * 2 ^ 59
def prefixEnd_2697345 : Nat := 4983230072969 + 3 ^ 40 * 2697345 * 2
def baseEnd_2697345 : Nat := 923356317334569572655095

theorem tailTrace_2697345 : CollatzResearch.WordTrace tailWord_2697345 prefixEnd_2697345 923356317334569572655095 := by
  unfold tailWord_2697345
  simp only [CollatzResearch.WordTrace]
  refine ⟨98380254412987209695309489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65586836275324806463539659 98380254412987209695309489)
  ·
    refine ⟨73785190809740407271482117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98380254412987209695309489 73785190809740407271482117)
    ·
      refine ⟨13834723276826326363402897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73785190809740407271482117 13834723276826326363402897)
      ·
        refine ⟨10376042457619744772552173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13834723276826326363402897 10376042457619744772552173)
        ·
          refine ⟨3891015921607404289707065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10376042457619744772552173 3891015921607404289707065)
          ·
            refine ⟨2918261941205553217280299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3891015921607404289707065 2918261941205553217280299)
            ·
              refine ⟨4377392911808329825920449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2918261941205553217280299 4377392911808329825920449)
              ·
                refine ⟨3283044683856247369440337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4377392911808329825920449 3283044683856247369440337)
                ·
                  refine ⟨2462283512892185527080253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3283044683856247369440337 2462283512892185527080253)
                  ·
                    refine ⟨923356317334569572655095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2462283512892185527080253 923356317334569572655095)
                    ·
                      rfl

theorem cell22_2697345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_2697345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697345 prefixEnd_2697345 := by exact prefixLift 2697345
  have htrace : WordTrace (prefixWord ++ tailWord_2697345) baseStart_2697345 baseEnd_2697345 := by
    simpa [prefixWord, tailWord_2697345, baseEnd_2697345] using wordTrace_append hprefix tailTrace_2697345
  have hstable : (prefixWord ++ tailWord_2697345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697345).length < 2 ^ (prefixWord ++ tailWord_2697345).sum := by decide
  have hdescent : baseEnd_2697345 < baseStart_2697345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697369 : List Nat := [1, 2, 1, 2, 1, 2, 1, 7, 5]
def baseStart_2697369 : Nat := 118140960795 + 2697369 * 2 ^ 59
def prefixEnd_2697369 : Nat := 4983230072969 + 3 ^ 40 * 2697369 * 2
def baseEnd_2697369 : Nat := 307788177675013836685007

theorem tailTrace_2697369 : CollatzResearch.WordTrace tailWord_2697369 prefixEnd_2697369 307788177675013836685007 := by
  unfold tailWord_2697369
  simp only [CollatzResearch.WordTrace]
  refine ⟨98381129764900261794183161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65587419843266841196122107 98381129764900261794183161)
  ·
    refine ⟨73785847323675196345637371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98381129764900261794183161 73785847323675196345637371)
    ·
      refine ⟨110678770985512794518456057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73785847323675196345637371 110678770985512794518456057)
      ·
        refine ⟨83009078239134595888842043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110678770985512794518456057 83009078239134595888842043)
        ·
          refine ⟨124513617358701893833263065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83009078239134595888842043 124513617358701893833263065)
          ·
            refine ⟨93385213019026420374947299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124513617358701893833263065 93385213019026420374947299)
            ·
              refine ⟨140077819528539630562420949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93385213019026420374947299 140077819528539630562420949)
              ·
                refine ⟨3283073895200147591306741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 140077819528539630562420949 3283073895200147591306741)
                ·
                  refine ⟨307788177675013836685007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3283073895200147591306741 307788177675013836685007)
                  ·
                    rfl

theorem cell22_2697369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 5].length) (baseStart_2697369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697369 prefixEnd_2697369 := by exact prefixLift 2697369
  have htrace : WordTrace (prefixWord ++ tailWord_2697369) baseStart_2697369 baseEnd_2697369 := by
    simpa [prefixWord, tailWord_2697369, baseEnd_2697369] using wordTrace_append hprefix tailTrace_2697369
  have hstable : (prefixWord ++ tailWord_2697369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697369).length < 2 ^ (prefixWord ++ tailWord_2697369).sum := by decide
  have hdescent : baseEnd_2697369 < baseStart_2697369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697514 : List Nat := [3, 1, 4, 2, 3, 1, 1, 2, 2, 3]
def baseStart_2697514 : Nat := 118140960795 + 2697514 * 2 ^ 59
def prefixEnd_2697514 : Nat := 4983230072969 + 3 ^ 40 * 2697514 * 2
def baseEnd_2697514 : Nat := 923414169488309465179577

theorem tailTrace_2697514 : CollatzResearch.WordTrace tailWord_2697514 prefixEnd_2697514 923414169488309465179577 := by
  unfold tailWord_2697514
  simp only [CollatzResearch.WordTrace]
  refine ⟨24596604587343737889552899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65590945566249967705474397 24596604587343737889552899)
  ·
    refine ⟨36894906881015606834329349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24596604587343737889552899 36894906881015606834329349)
    ·
      refine ⟨6917795040190426281436753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36894906881015606834329349 6917795040190426281436753)
      ·
        refine ⟨5188346280142819711077565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6917795040190426281436753 5188346280142819711077565)
        ·
          refine ⟨1945629855053557391654087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5188346280142819711077565 1945629855053557391654087)
          ·
            refine ⟨2918444782580336087481131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1945629855053557391654087 2918444782580336087481131)
            ·
              refine ⟨4377667173870504131221697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2918444782580336087481131 4377667173870504131221697)
              ·
                refine ⟨3283250380402878098416273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4377667173870504131221697 3283250380402878098416273)
                ·
                  refine ⟨2462437785302158573812205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3283250380402878098416273 2462437785302158573812205)
                  ·
                    refine ⟨923414169488309465179577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2462437785302158573812205 923414169488309465179577)
                    ·
                      rfl

theorem cell22_2697514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_2697514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697514 prefixEnd_2697514 := by exact prefixLift 2697514
  have htrace : WordTrace (prefixWord ++ tailWord_2697514) baseStart_2697514 baseEnd_2697514 := by
    simpa [prefixWord, tailWord_2697514, baseEnd_2697514] using wordTrace_append hprefix tailTrace_2697514
  have hstable : (prefixWord ++ tailWord_2697514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697514).length < 2 ^ (prefixWord ++ tailWord_2697514).sum := by decide
  have hdescent : baseEnd_2697514 < baseStart_2697514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697525 : List Nat := [1, 3, 3, 1, 2, 1, 1, 6, 1, 3]
def baseStart_2697525 : Nat := 118140960795 + 2697525 * 2 ^ 59
def prefixEnd_2697525 : Nat := 4983230072969 + 3 ^ 40 * 2697525 * 2
def baseEnd_2697525 : Nat := 923417935013109103154543

theorem tailTrace_2697525 : CollatzResearch.WordTrace tailWord_2697525 prefixEnd_2697525 923417935013109103154543 := by
  unfold tailWord_2697525
  simp only [CollatzResearch.WordTrace]
  refine ⟨98386819552335100436862029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65591213034890066957908019 98386819552335100436862029)
  ·
    refine ⟨36895057332125662663823261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98386819552335100436862029 36895057332125662663823261)
    ·
      refine ⟨13835646499547123498933723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36895057332125662663823261 13835646499547123498933723)
      ·
        refine ⟨20753469749320685248400585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13835646499547123498933723 20753469749320685248400585)
        ·
          refine ⟨15565102311990513936300439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20753469749320685248400585 15565102311990513936300439)
          ·
            refine ⟨23347653467985770904450659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15565102311990513936300439 23347653467985770904450659)
            ·
              refine ⟨35021480201978656356675989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23347653467985770904450659 35021480201978656356675989)
              ·
                refine ⟨1641631884467749516719187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35021480201978656356675989 1641631884467749516719187)
                ·
                  refine ⟨2462447826701624275078781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641631884467749516719187 2462447826701624275078781)
                  ·
                    refine ⟨923417935013109103154543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2462447826701624275078781 923417935013109103154543)
                    ·
                      rfl

theorem cell22_2697525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_2697525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697525 prefixEnd_2697525 := by exact prefixLift 2697525
  have htrace : WordTrace (prefixWord ++ tailWord_2697525) baseStart_2697525 baseEnd_2697525 := by
    simpa [prefixWord, tailWord_2697525, baseEnd_2697525] using wordTrace_append hprefix tailTrace_2697525
  have hstable : (prefixWord ++ tailWord_2697525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697525).length < 2 ^ (prefixWord ++ tailWord_2697525).sum := by decide
  have hdescent : baseEnd_2697525 < baseStart_2697525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697596 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 1, 6]
def baseStart_2697596 : Nat := 118140960795 + 2697596 * 2 ^ 59
def prefixEnd_2697596 : Nat := 4983230072969 + 3 ^ 40 * 2697596 * 2
def baseEnd_2697596 : Nat := 923442239764088584629325

theorem tailTrace_2697596 : CollatzResearch.WordTrace tailWord_2697596 prefixEnd_2697596 923442239764088584629325 := by
  unfold tailWord_2697596
  simp only [CollatzResearch.WordTrace]
  refine ⟨49194704567538939781348321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65592939423385253041797761 49194704567538939781348321)
  ·
    refine ⟨36896028425654204836011241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49194704567538939781348321 36896028425654204836011241)
    ·
      refine ⟨27672021319240653627008431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36896028425654204836011241 27672021319240653627008431)
      ·
        refine ⟨41508031978860980440512647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27672021319240653627008431 41508031978860980440512647)
        ·
          refine ⟨62262047968291470660768971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41508031978860980440512647 62262047968291470660768971)
          ·
            refine ⟨93393071952437205991153457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62262047968291470660768971 93393071952437205991153457)
            ·
              refine ⟨70044803964327904493365093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93393071952437205991153457 70044803964327904493365093)
              ·
                refine ⟨13133400743311482092505955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70044803964327904493365093 13133400743311482092505955)
                ·
                  refine ⟨19700101114967223138758933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13133400743311482092505955 19700101114967223138758933)
                  ·
                    refine ⟨923442239764088584629325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19700101114967223138758933 923442239764088584629325)
                    ·
                      rfl

theorem cell22_2697596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_2697596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697596 prefixEnd_2697596 := by exact prefixLift 2697596
  have htrace : WordTrace (prefixWord ++ tailWord_2697596) baseStart_2697596 baseEnd_2697596 := by
    simpa [prefixWord, tailWord_2697596, baseEnd_2697596] using wordTrace_append hprefix tailTrace_2697596
  have hstable : (prefixWord ++ tailWord_2697596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697596).length < 2 ^ (prefixWord ++ tailWord_2697596).sum := by decide
  have hdescent : baseEnd_2697596 < baseStart_2697596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697602 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_2697602 : Nat := 118140960795 + 2697602 * 2 ^ 59
def prefixEnd_2697602 : Nat := 4983230072969 + 3 ^ 40 * 2697602 * 2
def baseEnd_2697602 : Nat := 923444293686706568979307

theorem tailTrace_2697602 : CollatzResearch.WordTrace tailWord_2697602 prefixEnd_2697602 923444293686706568979307 := by
  unfold tailWord_2697602
  simp only [CollatzResearch.WordTrace]
  refine ⟨24597406993264035646853765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65593085315370761724943373 24597406993264035646853765)
  ·
    refine ⟨4612013811237006683785081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24597406993264035646853765 4612013811237006683785081)
    ·
      refine ⟨3459010358427755012838811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4612013811237006683785081 3459010358427755012838811)
      ·
        refine ⟨5188515537641632519258217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3459010358427755012838811 5188515537641632519258217)
        ·
          refine ⟨3891386653231224389443663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5188515537641632519258217 3891386653231224389443663)
          ·
            refine ⟨5837079979846836584165495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3891386653231224389443663 5837079979846836584165495)
            ·
              refine ⟨8755619969770254876248243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5837079979846836584165495 8755619969770254876248243)
              ·
                refine ⟨13133429954655382314372365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8755619969770254876248243 13133429954655382314372365)
                ·
                  refine ⟨4925036232995768367889637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13133429954655382314372365 4925036232995768367889637)
                  ·
                    refine ⟨923444293686706568979307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4925036232995768367889637 923444293686706568979307)
                    ·
                      rfl

theorem cell22_2697602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_2697602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697602 prefixEnd_2697602 := by exact prefixLift 2697602
  have htrace : WordTrace (prefixWord ++ tailWord_2697602) baseStart_2697602 baseEnd_2697602 := by
    simpa [prefixWord, tailWord_2697602, baseEnd_2697602] using wordTrace_append hprefix tailTrace_2697602
  have hstable : (prefixWord ++ tailWord_2697602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697602).length < 2 ^ (prefixWord ++ tailWord_2697602).sum := by decide
  have hdescent : baseEnd_2697602 < baseStart_2697602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697611 : List Nat := [1, 1, 1, 1, 4, 4, 2, 8]
def baseStart_2697611 : Nat := 118140960795 + 2697611 * 2 ^ 59
def prefixEnd_2697611 : Nat := 4983230072969 + 3 ^ 40 * 2697611 * 2
def baseEnd_2697611 : Nat := 102605263841181505056031

theorem tailTrace_2697611 : CollatzResearch.WordTrace tailWord_2697611 prefixEnd_2697611 102605263841181505056031 := by
  unfold tailWord_2697611
  simp only [CollatzResearch.WordTrace]
  refine ⟨98389956230023537124492687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65593304153349024749661791 98389956230023537124492687)
  ·
    refine ⟨147584934345035305686739031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98389956230023537124492687 147584934345035305686739031)
    ·
      refine ⟨221377401517552958530108547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147584934345035305686739031 221377401517552958530108547)
      ·
        refine ⟨332066102276329437795162821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221377401517552958530108547 332066102276329437795162821)
        ·
          refine ⟨62262394176811769586593029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 332066102276329437795162821 62262394176811769586593029)
          ·
            refine ⟨11674198908152206797486193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62262394176811769586593029 11674198908152206797486193)
            ·
              refine ⟨8755649181114155098114645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11674198908152206797486193 8755649181114155098114645)
              ·
                refine ⟨102605263841181505056031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8755649181114155098114645 102605263841181505056031)
                ·
                  rfl

theorem cell22_2697611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 8].length) (baseStart_2697611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697611 prefixEnd_2697611 := by exact prefixLift 2697611
  have htrace : WordTrace (prefixWord ++ tailWord_2697611) baseStart_2697611 baseEnd_2697611 := by
    simpa [prefixWord, tailWord_2697611, baseEnd_2697611] using wordTrace_append hprefix tailTrace_2697611
  have hstable : (prefixWord ++ tailWord_2697611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697611).length < 2 ^ (prefixWord ++ tailWord_2697611).sum := by decide
  have hdescent : baseEnd_2697611 < baseStart_2697611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697656 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 9]
def baseStart_2697656 : Nat := 118140960795 + 2697656 * 2 ^ 59
def prefixEnd_2697656 : Nat := 4983230072969 + 3 ^ 40 * 2697656 * 2
def baseEnd_2697656 : Nat := 307820926330089476043047

theorem tailTrace_2697656 : CollatzResearch.WordTrace tailWord_2697656 prefixEnd_2697656 307820926330089476043047 := by
  unfold tailWord_2697656
  simp only [CollatzResearch.WordTrace]
  refine ⟨49195798757430254904940411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65594398343240339873253881 49195798757430254904940411)
  ·
    refine ⟨73793698136145382357410617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49195798757430254904940411 73793698136145382357410617)
    ·
      refine ⟨55345273602109036768057963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73793698136145382357410617 55345273602109036768057963)
      ·
        refine ⟨83017910403163555152086945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55345273602109036768057963 83017910403163555152086945)
        ·
          refine ⟨62263432802372666364065209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83017910403163555152086945 62263432802372666364065209)
          ·
            refine ⟨46697574601779499773048907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62263432802372666364065209 46697574601779499773048907)
            ·
              refine ⟨70046361902669249659573361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46697574601779499773048907 70046361902669249659573361)
              ·
                refine ⟨52534771427001937244680021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70046361902669249659573361 52534771427001937244680021)
                ·
                  refine ⟨307820926330089476043047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52534771427001937244680021 307820926330089476043047)
                  ·
                    rfl

theorem cell22_2697656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 9].length) (baseStart_2697656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697656 prefixEnd_2697656 := by exact prefixLift 2697656
  have htrace : WordTrace (prefixWord ++ tailWord_2697656) baseStart_2697656 baseEnd_2697656 := by
    simpa [prefixWord, tailWord_2697656, baseEnd_2697656] using wordTrace_append hprefix tailTrace_2697656
  have hstable : (prefixWord ++ tailWord_2697656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697656).length < 2 ^ (prefixWord ++ tailWord_2697656).sum := by decide
  have hdescent : baseEnd_2697656 < baseStart_2697656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697660 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 5, 3]
def baseStart_2697660 : Nat := 118140960795 + 2697660 * 2 ^ 59
def prefixEnd_2697660 : Nat := 4983230072969 + 3 ^ 40 * 2697660 * 2
def baseEnd_2697660 : Nat := 923464148272013751029129

theorem tailTrace_2697660 : CollatzResearch.WordTrace tailWord_2697660 prefixEnd_2697660 923464148272013751029129 := by
  unfold tailWord_2697660
  simp only [CollatzResearch.WordTrace]
  refine ⟨49195871703423009246513217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65594495604564012328684289 49195871703423009246513217)
  ·
    refine ⟨36896903777567256934884913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49195871703423009246513217 36896903777567256934884913)
    ·
      refine ⟨27672677833175442701163685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36896903777567256934884913 27672677833175442701163685)
      ·
        refine ⟨5188627093720395506468191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27672677833175442701163685 5188627093720395506468191)
        ·
          refine ⟨7782940640580593259702287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5188627093720395506468191 7782940640580593259702287)
          ·
            refine ⟨11674410960870889889553431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7782940640580593259702287 11674410960870889889553431)
            ·
              refine ⟨17511616441306334834330147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11674410960870889889553431 17511616441306334834330147)
              ·
                refine ⟨26267424661959502251495221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17511616441306334834330147 26267424661959502251495221)
                ·
                  refine ⟨2462571062058703336077677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26267424661959502251495221 2462571062058703336077677)
                  ·
                    refine ⟨923464148272013751029129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2462571062058703336077677 923464148272013751029129)
                    ·
                      rfl

theorem cell22_2697660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_2697660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697660 prefixEnd_2697660 := by exact prefixLift 2697660
  have htrace : WordTrace (prefixWord ++ tailWord_2697660) baseStart_2697660 baseEnd_2697660 := by
    simpa [prefixWord, tailWord_2697660, baseEnd_2697660] using wordTrace_append hprefix tailTrace_2697660
  have hstable : (prefixWord ++ tailWord_2697660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697660).length < 2 ^ (prefixWord ++ tailWord_2697660).sum := by decide
  have hdescent : baseEnd_2697660 < baseStart_2697660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697720 : List Nat := [2, 1, 2, 1, 1, 4, 4, 2, 1, 4]
def baseStart_2697720 : Nat := 118140960795 + 2697720 * 2 ^ 59
def prefixEnd_2697720 : Nat := 4983230072969 + 3 ^ 40 * 2697720 * 2
def baseEnd_2697720 : Nat := 923484687498193594528945

theorem tailTrace_2697720 : CollatzResearch.WordTrace tailWord_2697720 prefixEnd_2697720 923484687498193594528945 := by
  unfold tailWord_2697720
  simp only [CollatzResearch.WordTrace]
  refine ⟨49196965893314324370105307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65595954524419099160140409 49196965893314324370105307)
  ·
    refine ⟨73795448839971486555157961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49196965893314324370105307 73795448839971486555157961)
    ·
      refine ⟨55346586629978614916368471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73795448839971486555157961 55346586629978614916368471)
      ·
        refine ⟨83019879944967922374552707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55346586629978614916368471 83019879944967922374552707)
        ·
          refine ⟨124529819917451883561829061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83019879944967922374552707 124529819917451883561829061)
          ·
            refine ⟨23349341234522228167842949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124529819917451883561829061 23349341234522228167842949)
            ·
              refine ⟨4378001481472917781470553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23349341234522228167842949 4378001481472917781470553)
              ·
                refine ⟨3283501111104688336102915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4378001481472917781470553 3283501111104688336102915)
                ·
                  refine ⟨4925251666657032504154373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3283501111104688336102915 4925251666657032504154373)
                  ·
                    refine ⟨923484687498193594528945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4925251666657032504154373 923484687498193594528945)
                    ·
                      rfl

theorem cell22_2697720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_2697720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697720 prefixEnd_2697720 := by exact prefixLift 2697720
  have htrace : WordTrace (prefixWord ++ tailWord_2697720) baseStart_2697720 baseEnd_2697720 := by
    simpa [prefixWord, tailWord_2697720, baseEnd_2697720] using wordTrace_append hprefix tailTrace_2697720
  have hstable : (prefixWord ++ tailWord_2697720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697720).length < 2 ^ (prefixWord ++ tailWord_2697720).sum := by decide
  have hdescent : baseEnd_2697720 < baseStart_2697720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697733 : List Nat := [1, 3, 1, 1, 2, 2, 2, 4, 1, 5]
def baseStart_2697733 : Nat := 118140960795 + 2697733 * 2 ^ 59
def prefixEnd_2697733 : Nat := 4983230072969 + 3 ^ 40 * 2697733 * 2
def baseEnd_2697733 : Nat := 923489137663865893953905

theorem tailTrace_2697733 : CollatzResearch.WordTrace tailWord_2697733 prefixEnd_2697733 923489137663865893953905 := by
  unfold tailWord_2697733
  simp only [CollatzResearch.WordTrace]
  refine ⟨98394405935581551960433853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65596270623721034640289235 98394405935581551960433853)
  ·
    refine ⟨36897902225843081985162695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98394405935581551960433853 36897902225843081985162695)
    ·
      refine ⟨55346853338764622977744043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36897902225843081985162695 55346853338764622977744043)
      ·
        refine ⟨83020280008146934466616065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55346853338764622977744043 83020280008146934466616065)
        ·
          refine ⟨62265210006110200849962049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83020280008146934466616065 62265210006110200849962049)
          ·
            refine ⟨46698907504582650637471537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62265210006110200849962049 46698907504582650637471537)
            ·
              refine ⟨35024180628436987978103653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46698907504582650637471537 35024180628436987978103653)
              ·
                refine ⟨6567033867831935245894435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35024180628436987978103653 6567033867831935245894435)
                ·
                  refine ⟨9850550801747902868841653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6567033867831935245894435 9850550801747902868841653)
                  ·
                    refine ⟨923489137663865893953905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9850550801747902868841653 923489137663865893953905)
                    ·
                      rfl

theorem cell22_2697733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_2697733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697733 prefixEnd_2697733 := by exact prefixLift 2697733
  have htrace : WordTrace (prefixWord ++ tailWord_2697733) baseStart_2697733 baseEnd_2697733 := by
    simpa [prefixWord, tailWord_2697733, baseEnd_2697733] using wordTrace_append hprefix tailTrace_2697733
  have hstable : (prefixWord ++ tailWord_2697733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697733).length < 2 ^ (prefixWord ++ tailWord_2697733).sum := by decide
  have hdescent : baseEnd_2697733 < baseStart_2697733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697763 : List Nat := [1, 1, 1, 4, 4, 1, 1, 9]
def baseStart_2697763 : Nat := 118140960795 + 2697763 * 2 ^ 59
def prefixEnd_2697763 : Nat := 4983230072969 + 3 ^ 40 * 2697763 * 2
def baseEnd_2697763 : Nat := 102611045252995090633757

theorem tailTrace_2697763 : CollatzResearch.WordTrace tailWord_2697763 prefixEnd_2697763 102611045252995090633757 := by
  unfold tailWord_2697763
  simp only [CollatzResearch.WordTrace]
  refine ⟨98395500125472867084025943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65597000083648578056017295 98395500125472867084025943)
  ·
    refine ⟨147593250188209300626038915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98395500125472867084025943 147593250188209300626038915)
    ·
      refine ⟨221389875282313950939058373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147593250188209300626038915 221389875282313950939058373)
      ·
        refine ⟨41510601615433865801073445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221389875282313950939058373 41510601615433865801073445)
        ·
          refine ⟨7783237802893849837701271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41510601615433865801073445 7783237802893849837701271)
          ·
            refine ⟨11674856704340774756551907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7783237802893849837701271 11674856704340774756551907)
            ·
              refine ⟨17512285056511162134827861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11674856704340774756551907 17512285056511162134827861)
              ·
                refine ⟨102611045252995090633757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17512285056511162134827861 102611045252995090633757)
                ·
                  rfl

theorem cell22_2697763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 9].length) (baseStart_2697763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697763 prefixEnd_2697763 := by exact prefixLift 2697763
  have htrace : WordTrace (prefixWord ++ tailWord_2697763) baseStart_2697763 baseEnd_2697763 := by
    simpa [prefixWord, tailWord_2697763, baseEnd_2697763] using wordTrace_append hprefix tailTrace_2697763
  have hstable : (prefixWord ++ tailWord_2697763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697763).length < 2 ^ (prefixWord ++ tailWord_2697763).sum := by decide
  have hdescent : baseEnd_2697763 < baseStart_2697763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697778 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_2697778 : Nat := 118140960795 + 2697778 * 2 ^ 59
def prefixEnd_2697778 : Nat := 4983230072969 + 3 ^ 40 * 2697778 * 2
def baseEnd_2697778 : Nat := 923504542083500776578767

theorem tailTrace_2697778 : CollatzResearch.WordTrace tailWord_2697778 prefixEnd_2697778 923504542083500776578767 := by
  unfold tailWord_2697778
  simp only [CollatzResearch.WordTrace]
  refine ⟨24599011805104631161455497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65597364813612349763881325 24599011805104631161455497)
  ·
    refine ⟨18449258853828473371091623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24599011805104631161455497 18449258853828473371091623)
    ·
      refine ⟨27673888280742710056637435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18449258853828473371091623 27673888280742710056637435)
      ·
        refine ⟨41510832421114065084956153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27673888280742710056637435 41510832421114065084956153)
        ·
          refine ⟨31133124315835548813717115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41510832421114065084956153 31133124315835548813717115)
          ·
            refine ⟨46699686473753323220575673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31133124315835548813717115 46699686473753323220575673)
            ·
              refine ⟨35024764855314992415431755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46699686473753323220575673 35024764855314992415431755)
              ·
                refine ⟨52537147282972488623147633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35024764855314992415431755 52537147282972488623147633)
                ·
                  refine ⟨39402860462229366467360725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52537147282972488623147633 39402860462229366467360725)
                  ·
                    refine ⟨923504542083500776578767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39402860462229366467360725 923504542083500776578767)
                    ·
                      rfl

theorem cell22_2697778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_2697778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697778 prefixEnd_2697778 := by exact prefixLift 2697778
  have htrace : WordTrace (prefixWord ++ tailWord_2697778) baseStart_2697778 baseEnd_2697778 := by
    simpa [prefixWord, tailWord_2697778, baseEnd_2697778] using wordTrace_append hprefix tailTrace_2697778
  have hstable : (prefixWord ++ tailWord_2697778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697778).length < 2 ^ (prefixWord ++ tailWord_2697778).sum := by decide
  have hdescent : baseEnd_2697778 < baseStart_2697778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697782 : List Nat := [5, 1, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_2697782 : Nat := 118140960795 + 2697782 * 2 ^ 59
def prefixEnd_2697782 : Nat := 4983230072969 + 3 ^ 40 * 2697782 * 2
def baseEnd_2697782 : Nat := 923505911365246099478755

theorem tailTrace_2697782 : CollatzResearch.WordTrace tailWord_2697782 prefixEnd_2697782 923505911365246099478755 := by
  unfold tailWord_2697782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6149762069525252083060475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65597462074936022219311733 6149762069525252083060475)
  ·
    refine ⟨9224643104287878124590713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6149762069525252083060475 9224643104287878124590713)
    ·
      refine ⟨6918482328215908593443035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9224643104287878124590713 6918482328215908593443035)
      ·
        refine ⟨10377723492323862890164553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6918482328215908593443035 10377723492323862890164553)
        ·
          refine ⟨7783292619242897167623415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10377723492323862890164553 7783292619242897167623415)
          ·
            refine ⟨11674938928864345751435123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7783292619242897167623415 11674938928864345751435123)
            ·
              refine ⟨17512408393296518627152685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11674938928864345751435123 17512408393296518627152685)
              ·
                refine ⟨6567153147486194485182257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17512408393296518627152685 6567153147486194485182257)
                ·
                  refine ⟨4925364860614645863886693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6567153147486194485182257 4925364860614645863886693)
                  ·
                    refine ⟨923505911365246099478755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4925364860614645863886693 923505911365246099478755)
                    ·
                      rfl

theorem cell22_2697782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_2697782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697782 prefixEnd_2697782 := by exact prefixLift 2697782
  have htrace : WordTrace (prefixWord ++ tailWord_2697782) baseStart_2697782 baseEnd_2697782 := by
    simpa [prefixWord, tailWord_2697782, baseEnd_2697782] using wordTrace_append hprefix tailTrace_2697782
  have hstable : (prefixWord ++ tailWord_2697782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697782).length < 2 ^ (prefixWord ++ tailWord_2697782).sum := by decide
  have hdescent : baseEnd_2697782 < baseStart_2697782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697825 : List Nat := [1, 2, 3, 1, 1, 4, 2, 3, 5]
def baseStart_2697825 : Nat := 118140960795 + 2697825 * 2 ^ 59
def prefixEnd_2697825 : Nat := 4983230072969 + 3 ^ 40 * 2697825 * 2
def baseEnd_2697825 : Nat := 307840210381336106884541

theorem tailTrace_2697825 : CollatzResearch.WordTrace tailWord_2697825 prefixEnd_2697825 307840210381336106884541 := by
  unfold tailWord_2697825
  simp only [CollatzResearch.WordTrace]
  refine ⟨98397761451248251672782929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65598507634165501115188619 98397761451248251672782929)
  ·
    refine ⟨73798321088436188754587197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98397761451248251672782929 73798321088436188754587197)
    ·
      refine ⟨27674370408163570782970199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73798321088436188754587197 27674370408163570782970199)
      ·
        refine ⟨41511555612245356174455299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27674370408163570782970199 41511555612245356174455299)
        ·
          refine ⟨62267333418368034261682949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41511555612245356174455299 62267333418368034261682949)
          ·
            refine ⟨11675125015944006424065553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62267333418368034261682949 11675125015944006424065553)
            ·
              refine ⟨8756343761958004818049165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11675125015944006424065553 8756343761958004818049165)
              ·
                refine ⟨3283628910734251806768437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8756343761958004818049165 3283628910734251806768437)
                ·
                  refine ⟨307840210381336106884541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3283628910734251806768437 307840210381336106884541)
                  ·
                    rfl

theorem cell22_2697825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 5].length) (baseStart_2697825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697825 prefixEnd_2697825 := by exact prefixLift 2697825
  have htrace : WordTrace (prefixWord ++ tailWord_2697825) baseStart_2697825 baseEnd_2697825 := by
    simpa [prefixWord, tailWord_2697825, baseEnd_2697825] using wordTrace_append hprefix tailTrace_2697825
  have hstable : (prefixWord ++ tailWord_2697825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697825).length < 2 ^ (prefixWord ++ tailWord_2697825).sum := by decide
  have hdescent : baseEnd_2697825 < baseStart_2697825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697883 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 2, 10]
def baseStart_2697883 : Nat := 118140960795 + 2697883 * 2 ^ 59
def prefixEnd_2697883 : Nat := 4983230072969 + 3 ^ 40 * 2697883 * 2
def baseEnd_2697883 : Nat := 923540485729315502703445

theorem tailTrace_2697883 : CollatzResearch.WordTrace tailWord_2697883 prefixEnd_2697883 923540485729315502703445 := by
  unfold tailWord_2697883
  simp only [CollatzResearch.WordTrace]
  refine ⟨98399876885038127578394303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65599917923358751718929535 98399876885038127578394303)
  ·
    refine ⟨147599815327557191367591455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98399876885038127578394303 147599815327557191367591455)
    ·
      refine ⟨221399722991335787051387183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147599815327557191367591455 221399722991335787051387183)
      ·
        refine ⟨332099584487003680577080775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221399722991335787051387183 332099584487003680577080775)
        ·
          refine ⟨498149376730505520865621163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332099584487003680577080775 498149376730505520865621163)
          ·
            refine ⟨747224065095758281298431745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498149376730505520865621163 747224065095758281298431745)
            ·
              refine ⟨560418048821818710973823809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 747224065095758281298431745 560418048821818710973823809)
              ·
                refine ⟨420313536616364033230367857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560418048821818710973823809 420313536616364033230367857)
                ·
                  refine ⟨315235152462273024922775893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 420313536616364033230367857 315235152462273024922775893)
                  ·
                    refine ⟨923540485729315502703445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 315235152462273024922775893 923540485729315502703445)
                    ·
                      rfl

theorem cell22_2697883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 10].length) (baseStart_2697883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697883 prefixEnd_2697883 := by exact prefixLift 2697883
  have htrace : WordTrace (prefixWord ++ tailWord_2697883) baseStart_2697883 baseEnd_2697883 := by
    simpa [prefixWord, tailWord_2697883, baseEnd_2697883] using wordTrace_append hprefix tailTrace_2697883
  have hstable : (prefixWord ++ tailWord_2697883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697883).length < 2 ^ (prefixWord ++ tailWord_2697883).sum := by decide
  have hdescent : baseEnd_2697883 < baseStart_2697883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697889 : List Nat := [1, 2, 3, 3, 3, 1, 2, 2, 1, 4]
def baseStart_2697889 : Nat := 118140960795 + 2697889 * 2 ^ 59
def prefixEnd_2697889 : Nat := 4983230072969 + 3 ^ 40 * 2697889 * 2
def baseEnd_2697889 : Nat := 923542539651933487053427

theorem tailTrace_2697889 : CollatzResearch.WordTrace tailWord_2697889 prefixEnd_2697889 923542539651933487053427 := by
  unfold tailWord_2697889
  simp only [CollatzResearch.WordTrace]
  refine ⟨98400095723016390603112721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65600063815344260402075147 98400095723016390603112721)
  ·
    refine ⟨73800071792262292952334541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98400095723016390603112721 73800071792262292952334541)
    ·
      refine ⟨27675026922098359857125453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73800071792262292952334541 27675026922098359857125453)
      ·
        refine ⟨10378135095786884946422045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27675026922098359857125453 10378135095786884946422045)
        ·
          refine ⟨3891800660920081854908267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10378135095786884946422045 3891800660920081854908267)
          ·
            refine ⟨5837700991380122782362401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3891800660920081854908267 5837700991380122782362401)
            ·
              refine ⟨4378275743535092086771801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5837700991380122782362401 4378275743535092086771801)
              ·
                refine ⟨3283706807651319065078851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4378275743535092086771801 3283706807651319065078851)
                ·
                  refine ⟨4925560211476978597618277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3283706807651319065078851 4925560211476978597618277)
                  ·
                    refine ⟨923542539651933487053427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4925560211476978597618277 923542539651933487053427)
                    ·
                      rfl

theorem cell22_2697889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_2697889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697889 prefixEnd_2697889 := by exact prefixLift 2697889
  have htrace : WordTrace (prefixWord ++ tailWord_2697889) baseStart_2697889 baseEnd_2697889 := by
    simpa [prefixWord, tailWord_2697889, baseEnd_2697889] using wordTrace_append hprefix tailTrace_2697889
  have hstable : (prefixWord ++ tailWord_2697889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697889).length < 2 ^ (prefixWord ++ tailWord_2697889).sum := by decide
  have hdescent : baseEnd_2697889 < baseStart_2697889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697917 : List Nat := [1, 4, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_2697917 : Nat := 118140960795 + 2697917 * 2 ^ 59
def prefixEnd_2697917 : Nat := 4983230072969 + 3 ^ 40 * 2697917 * 2
def baseEnd_2697917 : Nat := 923552124624150747353341

theorem tailTrace_2697917 : CollatzResearch.WordTrace tailWord_2697917 prefixEnd_2697917 923552124624150747353341 := by
  unfold tailWord_2697917
  simp only [CollatzResearch.WordTrace]
  refine ⟨98401116966914951385132005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65600744644609967590088003 98401116966914951385132005)
  ·
    refine ⟨18450209431296553384712251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98401116966914951385132005 18450209431296553384712251)
    ·
      refine ⟨27675314146944830077068377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18450209431296553384712251 27675314146944830077068377)
      ·
        refine ⟨20756485610208622557801283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27675314146944830077068377 20756485610208622557801283)
        ·
          refine ⟨31134728415312933836701925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20756485610208622557801283 31134728415312933836701925)
          ·
            refine ⟨5837761577871175094381611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31134728415312933836701925 5837761577871175094381611)
            ·
              refine ⟨8756642366806762641572417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5837761577871175094381611 8756642366806762641572417)
              ·
                refine ⟨6567481775105071981179313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8756642366806762641572417 6567481775105071981179313)
                ·
                  refine ⟨4925611331328803985884485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6567481775105071981179313 4925611331328803985884485)
                  ·
                    refine ⟨923552124624150747353341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4925611331328803985884485 923552124624150747353341)
                    ·
                      rfl

theorem cell22_2697917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_2697917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697917 prefixEnd_2697917 := by exact prefixLift 2697917
  have htrace : WordTrace (prefixWord ++ tailWord_2697917) baseStart_2697917 baseEnd_2697917 := by
    simpa [prefixWord, tailWord_2697917, baseEnd_2697917] using wordTrace_append hprefix tailTrace_2697917
  have hstable : (prefixWord ++ tailWord_2697917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697917).length < 2 ^ (prefixWord ++ tailWord_2697917).sum := by decide
  have hdescent : baseEnd_2697917 < baseStart_2697917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697921 : List Nat := [1, 2, 6, 2, 1, 2, 1, 1, 6]
def baseStart_2697921 : Nat := 118140960795 + 2697921 * 2 ^ 59
def prefixEnd_2697921 : Nat := 4983230072969 + 3 ^ 40 * 2697921 * 2
def baseEnd_2697921 : Nat := 307851164635298690084443

theorem tailTrace_2697921 : CollatzResearch.WordTrace tailWord_2697921 prefixEnd_2697921 307851164635298690084443 := by
  unfold tailWord_2697921
  simp only [CollatzResearch.WordTrace]
  refine ⟨98401262858900460068277617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65600841905933640045518411 98401262858900460068277617)
  ·
    refine ⟨73800947144175345051208213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98401262858900460068277617 73800947144175345051208213)
    ·
      refine ⟨3459419397383219299275385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73800947144175345051208213 3459419397383219299275385)
      ·
        refine ⟨2594564548037414474456539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3459419397383219299275385 2594564548037414474456539)
        ·
          refine ⟨3891846822056121711684809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2594564548037414474456539 3891846822056121711684809)
          ·
            refine ⟨2918885116542091283763607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3891846822056121711684809 2918885116542091283763607)
            ·
              refine ⟨4378327674813136925645411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2918885116542091283763607 4378327674813136925645411)
              ·
                refine ⟨6567491512219705388468117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4378327674813136925645411 6567491512219705388468117)
                ·
                  refine ⟨307851164635298690084443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6567491512219705388468117 307851164635298690084443)
                  ·
                    rfl

theorem cell22_2697921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 6].length) (baseStart_2697921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697921 prefixEnd_2697921 := by exact prefixLift 2697921
  have htrace : WordTrace (prefixWord ++ tailWord_2697921) baseStart_2697921 baseEnd_2697921 := by
    simpa [prefixWord, tailWord_2697921, baseEnd_2697921] using wordTrace_append hprefix tailTrace_2697921
  have hstable : (prefixWord ++ tailWord_2697921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697921).length < 2 ^ (prefixWord ++ tailWord_2697921).sum := by decide
  have hdescent : baseEnd_2697921 < baseStart_2697921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697932 : List Nat := [2, 2, 1, 5, 1, 2, 2, 7]
def baseStart_2697932 : Nat := 118140960795 + 2697932 * 2 ^ 59
def prefixEnd_2697932 : Nat := 4983230072969 + 3 ^ 40 * 2697932 * 2
def baseEnd_2697932 : Nat := 102617473270077300914255

theorem tailTrace_2697932 : CollatzResearch.WordTrace tailWord_2697932 prefixEnd_2697932 102617473270077300914255 := by
  unfold tailWord_2697932
  simp only [CollatzResearch.WordTrace]
  refine ⟨49200832030930304473464025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65601109374573739297952033 49200832030930304473464025)
  ·
    refine ⟨36900624023197728355098019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49200832030930304473464025 36900624023197728355098019)
    ·
      refine ⟨55350936034796592532647029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36900624023197728355098019 55350936034796592532647029)
      ·
        refine ⟨5189150253262180549935659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55350936034796592532647029 5189150253262180549935659)
        ·
          refine ⟨7783725379893270824903489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5189150253262180549935659 7783725379893270824903489)
          ·
            refine ⟨5837794034919953118677617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7783725379893270824903489 5837794034919953118677617)
            ·
              refine ⟨4378345526189964839008213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5837794034919953118677617 4378345526189964839008213)
              ·
                refine ⟨102617473270077300914255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4378345526189964839008213 102617473270077300914255)
                ·
                  rfl

theorem cell22_2697932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 7].length) (baseStart_2697932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697932 prefixEnd_2697932 := by exact prefixLift 2697932
  have htrace : WordTrace (prefixWord ++ tailWord_2697932) baseStart_2697932 baseEnd_2697932 := by
    simpa [prefixWord, tailWord_2697932, baseEnd_2697932] using wordTrace_append hprefix tailTrace_2697932
  have hstable : (prefixWord ++ tailWord_2697932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697932).length < 2 ^ (prefixWord ++ tailWord_2697932).sum := by decide
  have hdescent : baseEnd_2697932 < baseStart_2697932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697964 : List Nat := [2, 2, 1, 1, 2, 2, 1, 7, 1, 3]
def baseStart_2697964 : Nat := 118140960795 + 2697964 * 2 ^ 59
def prefixEnd_2697964 : Nat := 4983230072969 + 3 ^ 40 * 2697964 * 2
def baseEnd_2697964 : Nat := 923568213684658291428197

theorem tailTrace_2697964 : CollatzResearch.WordTrace tailWord_2697964 prefixEnd_2697964 923568213684658291428197 := by
  unfold tailWord_2697964
  simp only [CollatzResearch.WordTrace]
  refine ⟨49201415598872339206046473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65601887465163118941395297 49201415598872339206046473)
  ·
    refine ⟨36901061699154254404534855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49201415598872339206046473 36901061699154254404534855)
    ·
      refine ⟨55351592548731381606802283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36901061699154254404534855 55351592548731381606802283)
      ·
        refine ⟨83027388823097072410203425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55351592548731381606802283 83027388823097072410203425)
        ·
          refine ⟨62270541617322804307652569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83027388823097072410203425 62270541617322804307652569)
          ·
            refine ⟨46702906212992103230739427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62270541617322804307652569 46702906212992103230739427)
            ·
              refine ⟨70054359319488154846109141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46702906212992103230739427 70054359319488154846109141)
              ·
                refine ⟨1641899046550503629205683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 70054359319488154846109141 1641899046550503629205683)
                ·
                  refine ⟨2462848569825755443808525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641899046550503629205683 2462848569825755443808525)
                  ·
                    refine ⟨923568213684658291428197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2462848569825755443808525 923568213684658291428197)
                    ·
                      rfl

theorem cell22_2697964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 1, 3].length) (baseStart_2697964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697964 prefixEnd_2697964 := by exact prefixLift 2697964
  have htrace : WordTrace (prefixWord ++ tailWord_2697964) baseStart_2697964 baseEnd_2697964 := by
    simpa [prefixWord, tailWord_2697964, baseEnd_2697964] using wordTrace_append hprefix tailTrace_2697964
  have hstable : (prefixWord ++ tailWord_2697964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697964).length < 2 ^ (prefixWord ++ tailWord_2697964).sum := by decide
  have hdescent : baseEnd_2697964 < baseStart_2697964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697972 : List Nat := [2, 6, 1, 1, 3, 1, 2, 2, 4]
def baseStart_2697972 : Nat := 118140960795 + 2697972 * 2 ^ 59
def prefixEnd_2697972 : Nat := 4983230072969 + 3 ^ 40 * 2697972 * 2
def baseEnd_2697972 : Nat := 307856984082716312409391

theorem tailTrace_2697972 : CollatzResearch.WordTrace tailWord_2697972 prefixEnd_2697972 307856984082716312409391 := by
  unfold tailWord_2697972
  simp only [CollatzResearch.WordTrace]
  refine ⟨49201561490857847889192085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65602081987810463852256113 49201561490857847889192085)
  ·
    refine ⟨2306323194883961619805879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49201561490857847889192085 2306323194883961619805879)
    ·
      refine ⟨3459484792325942429708819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2306323194883961619805879 3459484792325942429708819)
      ·
        refine ⟨5189227188488913644563229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3459484792325942429708819 5189227188488913644563229)
        ·
          refine ⟨1945960195683342616711211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5189227188488913644563229 1945960195683342616711211)
          ·
            refine ⟨2918940293525013925066817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1945960195683342616711211 2918940293525013925066817)
            ·
              refine ⟨2189205220143760443800113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2918940293525013925066817 2189205220143760443800113)
              ·
                refine ⟨1641903915107820332850085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2189205220143760443800113 1641903915107820332850085)
                ·
                  refine ⟨307856984082716312409391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1641903915107820332850085 307856984082716312409391)
                  ·
                    rfl

theorem cell22_2697972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_2697972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697972 prefixEnd_2697972 := by exact prefixLift 2697972
  have htrace : WordTrace (prefixWord ++ tailWord_2697972) baseStart_2697972 baseEnd_2697972 := by
    simpa [prefixWord, tailWord_2697972, baseEnd_2697972] using wordTrace_append hprefix tailTrace_2697972
  have hstable : (prefixWord ++ tailWord_2697972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697972).length < 2 ^ (prefixWord ++ tailWord_2697972).sum := by decide
  have hdescent : baseEnd_2697972 < baseStart_2697972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697975 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 2, 5]
def baseStart_2697975 : Nat := 118140960795 + 2697975 * 2 ^ 59
def prefixEnd_2697975 : Nat := 4983230072969 + 3 ^ 40 * 2697975 * 2
def baseEnd_2697975 : Nat := 923571979209457929403163

theorem tailTrace_2697975 : CollatzResearch.WordTrace tailWord_2697975 prefixEnd_2697975 923571979209457929403163 := by
  unfold tailWord_2697975
  simp only [CollatzResearch.WordTrace]
  refine ⟨98403232400704827290743379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65602154933803218193828919 98403232400704827290743379)
  ·
    refine ⟨147604848601057240936115069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98403232400704827290743379 147604848601057240936115069)
    ·
      refine ⟨55351818225396465351043151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147604848601057240936115069 55351818225396465351043151)
      ·
        refine ⟨83027727338094698026564727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55351818225396465351043151 83027727338094698026564727)
        ·
          refine ⟨124541591007142047039847091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83027727338094698026564727 124541591007142047039847091)
          ·
            refine ⟨186812386510713070559770637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124541591007142047039847091 186812386510713070559770637)
            ·
              refine ⟨70054644941517401459913989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186812386510713070559770637 70054644941517401459913989)
              ·
                refine ⟨13135245926534512773733873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70054644941517401459913989 13135245926534512773733873)
                ·
                  refine ⟨9851434444900884580300405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13135245926534512773733873 9851434444900884580300405)
                  ·
                    refine ⟨923571979209457929403163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9851434444900884580300405 923571979209457929403163)
                    ·
                      rfl

theorem cell22_2697975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_2697975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697975 prefixEnd_2697975 := by exact prefixLift 2697975
  have htrace : WordTrace (prefixWord ++ tailWord_2697975) baseStart_2697975 baseEnd_2697975 := by
    simpa [prefixWord, tailWord_2697975, baseEnd_2697975] using wordTrace_append hprefix tailTrace_2697975
  have hstable : (prefixWord ++ tailWord_2697975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697975).length < 2 ^ (prefixWord ++ tailWord_2697975).sum := by decide
  have hdescent : baseEnd_2697975 < baseStart_2697975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697992 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 2, 5]
def baseStart_2697992 : Nat := 118140960795 + 2697992 * 2 ^ 59
def prefixEnd_2697992 : Nat := 4983230072969 + 3 ^ 40 * 2697992 * 2
def baseEnd_2697992 : Nat := 923577798656875551728111

theorem tailTrace_2697992 : CollatzResearch.WordTrace tailWord_2697992 prefixEnd_2697992 923577798656875551728111 := by
  unfold tailWord_2697992
  simp only [CollatzResearch.WordTrace]
  refine ⟨49201926220821619597056115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65602568294428826129408153 49201926220821619597056115)
  ·
    refine ⟨73802889331232429395584173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49201926220821619597056115 73802889331232429395584173)
    ·
      refine ⟨27676083499212161023344065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73802889331232429395584173 27676083499212161023344065)
      ·
        refine ⟨20757062624409120767508049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27676083499212161023344065 20757062624409120767508049)
        ·
          refine ⟨15567796968306840575631037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20757062624409120767508049 15567796968306840575631037)
          ·
            refine ⟨5837923863115065215861639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15567796968306840575631037 5837923863115065215861639)
            ·
              refine ⟨8756885794672597823792459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5837923863115065215861639 8756885794672597823792459)
              ·
                refine ⟨13135328692008896735688689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8756885794672597823792459 13135328692008896735688689)
                ·
                  refine ⟨9851496519006672551766517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13135328692008896735688689 9851496519006672551766517)
                  ·
                    refine ⟨923577798656875551728111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9851496519006672551766517 923577798656875551728111)
                    ·
                      rfl

theorem cell22_2697992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_2697992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2697992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2697992 prefixEnd_2697992 := by exact prefixLift 2697992
  have htrace : WordTrace (prefixWord ++ tailWord_2697992) baseStart_2697992 baseEnd_2697992 := by
    simpa [prefixWord, tailWord_2697992, baseEnd_2697992] using wordTrace_append hprefix tailTrace_2697992
  have hstable : (prefixWord ++ tailWord_2697992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697992).length < 2 ^ (prefixWord ++ tailWord_2697992).sum := by decide
  have hdescent : baseEnd_2697992 < baseStart_2697992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698024 : List Nat := [2, 1, 5, 1, 1, 1, 3, 3, 1, 4]
def baseStart_2698024 : Nat := 118140960795 + 2698024 * 2 ^ 59
def prefixEnd_2698024 : Nat := 4983230072969 + 3 ^ 40 * 2698024 * 2
def baseEnd_2698024 : Nat := 923588752910838134928013

theorem tailTrace_2698024 : CollatzResearch.WordTrace tailWord_2698024 prefixEnd_2698024 923588752910838134928013 := by
  unfold tailWord_2698024
  simp only [CollatzResearch.WordTrace]
  refine ⟨49202509788763654329638563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65603346385018205772851417 49202509788763654329638563)
  ·
    refine ⟨73803764683145481494457845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49202509788763654329638563 73803764683145481494457845)
    ·
      refine ⟨6919102939044888890105423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73803764683145481494457845 6919102939044888890105423)
      ·
        refine ⟨10378654408567333335158135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6919102939044888890105423 10378654408567333335158135)
        ·
          refine ⟨15567981612851000002737203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10378654408567333335158135 15567981612851000002737203)
          ·
            refine ⟨23351972419276500004105805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15567981612851000002737203 23351972419276500004105805)
            ·
              refine ⟨8756989657228687501539677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23351972419276500004105805 8756989657228687501539677)
              ·
                refine ⟨3283871121460757813077379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8756989657228687501539677 3283871121460757813077379)
                ·
                  refine ⟨4925806682191136719616069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3283871121460757813077379 4925806682191136719616069)
                  ·
                    refine ⟨923588752910838134928013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4925806682191136719616069 923588752910838134928013)
                    ·
                      rfl

theorem cell22_2698024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_2698024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698024 prefixEnd_2698024 := by exact prefixLift 2698024
  have htrace : WordTrace (prefixWord ++ tailWord_2698024) baseStart_2698024 baseEnd_2698024 := by
    simpa [prefixWord, tailWord_2698024, baseEnd_2698024] using wordTrace_append hprefix tailTrace_2698024
  have hstable : (prefixWord ++ tailWord_2698024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698024).length < 2 ^ (prefixWord ++ tailWord_2698024).sum := by decide
  have hdescent : baseEnd_2698024 < baseStart_2698024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698099 : List Nat := [1, 1, 1, 2, 2, 1, 7, 1, 3, 3]
def baseStart_2698099 : Nat := 118140960795 + 2698099 * 2 ^ 59
def prefixEnd_2698099 : Nat := 4983230072969 + 3 ^ 40 * 2698099 * 2
def baseEnd_2698099 : Nat := 923614426943562939302783

theorem tailTrace_2698099 : CollatzResearch.WordTrace tailWord_2698099 prefixEnd_2698099 923614426943562939302783 := by
  unfold tailWord_2698099
  simp only [CollatzResearch.WordTrace]
  refine ⟨98407755052255596468257351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65605170034837064312171567 98407755052255596468257351)
  ·
    refine ⟨147611632578383394702386027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98407755052255596468257351 147611632578383394702386027)
    ·
      refine ⟨221417448867575092053579041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147611632578383394702386027 221417448867575092053579041)
      ·
        refine ⟨166063086650681319040184281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221417448867575092053579041 166063086650681319040184281)
        ·
          refine ⟨124547314988010989280138211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166063086650681319040184281 124547314988010989280138211)
          ·
            refine ⟨186820972482016483920207317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124547314988010989280138211 186820972482016483920207317)
            ·
              refine ⟨4378616542547261341879859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 186820972482016483920207317 4378616542547261341879859)
              ·
                refine ⟨6567924813820892012819789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4378616542547261341879859 6567924813820892012819789)
                ·
                  refine ⟨2462971805182834504807421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6567924813820892012819789 2462971805182834504807421)
                  ·
                    refine ⟨923614426943562939302783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2462971805182834504807421 923614426943562939302783)
                    ·
                      rfl

theorem cell22_2698099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 3].length) (baseStart_2698099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698099 prefixEnd_2698099 := by exact prefixLift 2698099
  have htrace : WordTrace (prefixWord ++ tailWord_2698099) baseStart_2698099 baseEnd_2698099 := by
    simpa [prefixWord, tailWord_2698099, baseEnd_2698099] using wordTrace_append hprefix tailTrace_2698099
  have hstable : (prefixWord ++ tailWord_2698099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698099).length < 2 ^ (prefixWord ++ tailWord_2698099).sum := by decide
  have hdescent : baseEnd_2698099 < baseStart_2698099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698146 : List Nat := [3, 3, 1, 2, 2, 2, 2, 2, 5]
def baseStart_2698146 : Nat := 118140960795 + 2698146 * 2 ^ 59
def prefixEnd_2698146 : Nat := 4983230072969 + 3 ^ 40 * 2698146 * 2
def baseEnd_2698146 : Nat := 307876838668023494459213

theorem tailTrace_2698146 : CollatzResearch.WordTrace tailWord_2698146 prefixEnd_2698146 307876838668023494459213 := by
  unfold tailWord_2698146
  simp only [CollatzResearch.WordTrace]
  refine ⟨24602367320771330873804573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65606312855390215663478861 24602367320771330873804573)
  ·
    refine ⟨9225887745289249077676715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24602367320771330873804573 9225887745289249077676715)
    ·
      refine ⟨13838831617933873616515073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9225887745289249077676715 13838831617933873616515073)
      ·
        refine ⟨10379123713450405212386305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13838831617933873616515073 10379123713450405212386305)
        ·
          refine ⟨7784342785087803909289729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10379123713450405212386305 7784342785087803909289729)
          ·
            refine ⟨5838257088815852931967297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7784342785087803909289729 5838257088815852931967297)
            ·
              refine ⟨4378692816611889698975473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5838257088815852931967297 4378692816611889698975473)
              ·
                refine ⟨3284019612458917274231605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4378692816611889698975473 3284019612458917274231605)
                ·
                  refine ⟨307876838668023494459213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3284019612458917274231605 307876838668023494459213)
                  ·
                    rfl

theorem cell22_2698146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_2698146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698146 prefixEnd_2698146 := by exact prefixLift 2698146
  have htrace : WordTrace (prefixWord ++ tailWord_2698146) baseStart_2698146 baseEnd_2698146 := by
    simpa [prefixWord, tailWord_2698146, baseEnd_2698146] using wordTrace_append hprefix tailTrace_2698146
  have hstable : (prefixWord ++ tailWord_2698146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698146).length < 2 ^ (prefixWord ++ tailWord_2698146).sum := by decide
  have hdescent : baseEnd_2698146 < baseStart_2698146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698174 : List Nat := [4, 2, 1, 1, 1, 2, 3, 2, 6]
def baseStart_2698174 : Nat := 118140960795 + 2698174 * 2 ^ 59
def prefixEnd_2698174 : Nat := 4983230072969 + 3 ^ 40 * 2698174 * 2
def baseEnd_2698174 : Nat := 307880033658762581225851

theorem tailTrace_2698174 : CollatzResearch.WordTrace tailWord_2698174 prefixEnd_2698174 307880033658762581225851 := by
  unfold tailWord_2698174
  simp only [CollatzResearch.WordTrace]
  refine ⟨12301311315872985534654697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65606993684655922851491717 12301311315872985534654697)
  ·
    refine ⟨9225983486904739150991023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12301311315872985534654697 9225983486904739150991023)
    ·
      refine ⟨13838975230357108726486535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9225983486904739150991023 13838975230357108726486535)
      ·
        refine ⟨20758462845535663089729803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13838975230357108726486535 20758462845535663089729803)
        ·
          refine ⟨31137694268303494634594705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20758462845535663089729803 31137694268303494634594705)
          ·
            refine ⟨23353270701227620975946029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31137694268303494634594705 23353270701227620975946029)
            ·
              refine ⟨8757476512960357865979761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23353270701227620975946029 8757476512960357865979761)
              ·
                refine ⟨6568107384720268399484821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8757476512960357865979761 6568107384720268399484821)
                ·
                  refine ⟨307880033658762581225851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6568107384720268399484821 307880033658762581225851)
                  ·
                    rfl

theorem cell22_2698174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_2698174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698174 prefixEnd_2698174 := by exact prefixLift 2698174
  have htrace : WordTrace (prefixWord ++ tailWord_2698174) baseStart_2698174 baseEnd_2698174 := by
    simpa [prefixWord, tailWord_2698174, baseEnd_2698174] using wordTrace_append hprefix tailTrace_2698174
  have hstable : (prefixWord ++ tailWord_2698174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698174).length < 2 ^ (prefixWord ++ tailWord_2698174).sum := by decide
  have hdescent : baseEnd_2698174 < baseStart_2698174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698191 : List Nat := [1, 1, 2, 1, 1, 7, 2, 3, 4]
def baseStart_2698191 : Nat := 118140960795 + 2698191 * 2 ^ 59
def prefixEnd_2698191 : Nat := 4983230072969 + 3 ^ 40 * 2698191 * 2
def baseEnd_2698191 : Nat := 307881973474568455334167

theorem tailTrace_2698191 : CollatzResearch.WordTrace tailWord_2698191 prefixEnd_2698191 307881973474568455334167 := by
  unfold tailWord_2698191
  simp only [CollatzResearch.WordTrace]
  refine ⟨98411110567922296180606427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65607407045281530787070951 98411110567922296180606427)
  ·
    refine ⟨147616665851883444270909641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98411110567922296180606427 147616665851883444270909641)
    ·
      refine ⟨110712499388912583203182231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147616665851883444270909641 110712499388912583203182231)
      ·
        refine ⟨166068749083368874804773347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110712499388912583203182231 166068749083368874804773347)
        ·
          refine ⟨249103123625053312207160021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166068749083368874804773347 249103123625053312207160021)
          ·
            refine ⟨5838354459962187004855313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 249103123625053312207160021 5838354459962187004855313)
            ·
              refine ⟨4378765844971640253641485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5838354459962187004855313 4378765844971640253641485)
              ·
                refine ⟨1642037191864365095115557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4378765844971640253641485 1642037191864365095115557)
                ·
                  refine ⟨307881973474568455334167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1642037191864365095115557 307881973474568455334167)
                  ·
                    rfl

theorem cell22_2698191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 4].length) (baseStart_2698191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698191 prefixEnd_2698191 := by exact prefixLift 2698191
  have htrace : WordTrace (prefixWord ++ tailWord_2698191) baseStart_2698191 baseEnd_2698191 := by
    simpa [prefixWord, tailWord_2698191, baseEnd_2698191] using wordTrace_append hprefix tailTrace_2698191
  have hstable : (prefixWord ++ tailWord_2698191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698191).length < 2 ^ (prefixWord ++ tailWord_2698191).sum := by decide
  have hdescent : baseEnd_2698191 < baseStart_2698191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698223 : List Nat := [1, 1, 2, 1, 4, 4, 3, 1, 2, 3]
def baseStart_2698223 : Nat := 118140960795 + 2698223 * 2 ^ 59
def prefixEnd_2698223 : Nat := 4983230072969 + 3 ^ 40 * 2698223 * 2
def baseEnd_2698223 : Nat := 923656874677667949202403

theorem tailTrace_2698223 : CollatzResearch.WordTrace tailWord_2698223 prefixEnd_2698223 923656874677667949202403 := by
  unfold tailWord_2698223
  simp only [CollatzResearch.WordTrace]
  refine ⟨98412277703806365645771323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65608185135870910430514215 98412277703806365645771323)
  ·
    refine ⟨147618416555709548468656985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98412277703806365645771323 147618416555709548468656985)
    ·
      refine ⟨110713812416782161351492739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147618416555709548468656985 110713812416782161351492739)
      ·
        refine ⟨166070718625173242027239109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110713812416782161351492739 166070718625173242027239109)
        ·
          refine ⟨31138259742219982880107333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166070718625173242027239109 31138259742219982880107333)
          ·
            refine ⟨5838423701666246790020125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31138259742219982880107333 5838423701666246790020125)
            ·
              refine ⟨2189408888124842546257547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5838423701666246790020125 2189408888124842546257547)
              ·
                refine ⟨3284113332187263819386321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2189408888124842546257547 3284113332187263819386321)
                ·
                  refine ⟨2463084999140447864539741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3284113332187263819386321 2463084999140447864539741)
                  ·
                    refine ⟨923656874677667949202403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2463084999140447864539741 923656874677667949202403)
                    ·
                      rfl

theorem cell22_2698223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 2, 3].length) (baseStart_2698223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698223 prefixEnd_2698223 := by exact prefixLift 2698223
  have htrace : WordTrace (prefixWord ++ tailWord_2698223) baseStart_2698223 baseEnd_2698223 := by
    simpa [prefixWord, tailWord_2698223, baseEnd_2698223] using wordTrace_append hprefix tailTrace_2698223
  have hstable : (prefixWord ++ tailWord_2698223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698223).length < 2 ^ (prefixWord ++ tailWord_2698223).sum := by decide
  have hdescent : baseEnd_2698223 < baseStart_2698223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698236 : List Nat := [2, 2, 2, 1, 2, 5, 2, 6]
def baseStart_2698236 : Nat := 118140960795 + 2698236 * 2 ^ 59
def prefixEnd_2698236 : Nat := 4983230072969 + 3 ^ 40 * 2698236 * 2
def baseEnd_2698236 : Nat := 102629036093704472069707

theorem tailTrace_2698236 : CollatzResearch.WordTrace tailWord_2698236 prefixEnd_2698236 102629036093704472069707 := by
  unfold tailWord_2698236
  simp only [CollatzResearch.WordTrace]
  refine ⟨49206375926379634432997281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65608501235172845910663041 49206375926379634432997281)
  ·
    refine ⟨36904781944784725824747961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49206375926379634432997281 36904781944784725824747961)
    ·
      refine ⟨27678586458588544368560971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36904781944784725824747961 27678586458588544368560971)
      ·
        refine ⟨41517879687882816552841457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27678586458588544368560971 41517879687882816552841457)
        ·
          refine ⟨31138409765912112414631093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41517879687882816552841457 31138409765912112414631093)
          ·
            refine ⟨2919225915554260538871665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31138409765912112414631093 2919225915554260538871665)
            ·
              refine ⟨2189419436665695404153749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2919225915554260538871665 2189419436665695404153749)
              ·
                refine ⟨102629036093704472069707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2189419436665695404153749 102629036093704472069707)
                ·
                  rfl

theorem cell22_2698236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 6].length) (baseStart_2698236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698236 prefixEnd_2698236 := by exact prefixLift 2698236
  have htrace : WordTrace (prefixWord ++ tailWord_2698236) baseStart_2698236 baseEnd_2698236 := by
    simpa [prefixWord, tailWord_2698236, baseEnd_2698236] using wordTrace_append hprefix tailTrace_2698236
  have hstable : (prefixWord ++ tailWord_2698236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698236).length < 2 ^ (prefixWord ++ tailWord_2698236).sum := by decide
  have hdescent : baseEnd_2698236 < baseStart_2698236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698242 : List Nat := [3, 4, 1, 3, 1, 2, 1, 3, 4]
def baseStart_2698242 : Nat := 118140960795 + 2698242 * 2 ^ 59
def prefixEnd_2698242 : Nat := 4983230072969 + 3 ^ 40 * 2698242 * 2
def baseEnd_2698242 : Nat := 307887792921986077659115

theorem tailTrace_2698242 : CollatzResearch.WordTrace tailWord_2698242 prefixEnd_2698242 307887792921986077659115 := by
  unfold tailWord_2698242
  simp only [CollatzResearch.WordTrace]
  refine ⟨24603242672684382972678245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65608647127158354593808653 24603242672684382972678245)
  ·
    refine ⟨4613108001128321807377171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24603242672684382972678245 4613108001128321807377171)
    ·
      refine ⟨6919662001692482711065757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4613108001128321807377171 6919662001692482711065757)
      ·
        refine ⟨2594873250634681016649659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6919662001692482711065757 2594873250634681016649659)
        ·
          refine ⟨3892309875952021524974489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2594873250634681016649659 3892309875952021524974489)
          ·
            refine ⟨2919232406964016143730867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3892309875952021524974489 2919232406964016143730867)
            ·
              refine ⟨4378848610446024215596301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2919232406964016143730867 4378848610446024215596301)
              ·
                refine ⟨1642068228917259080848613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4378848610446024215596301 1642068228917259080848613)
                ·
                  refine ⟨307887792921986077659115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1642068228917259080848613 307887792921986077659115)
                  ·
                    rfl

theorem cell22_2698242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_2698242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698242 prefixEnd_2698242 := by exact prefixLift 2698242
  have htrace : WordTrace (prefixWord ++ tailWord_2698242) baseStart_2698242 baseEnd_2698242 := by
    simpa [prefixWord, tailWord_2698242, baseEnd_2698242] using wordTrace_append hprefix tailTrace_2698242
  have hstable : (prefixWord ++ tailWord_2698242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698242).length < 2 ^ (prefixWord ++ tailWord_2698242).sum := by decide
  have hdescent : baseEnd_2698242 < baseStart_2698242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698264 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 7]
def baseStart_2698264 : Nat := 118140960795 + 2698264 * 2 ^ 59
def prefixEnd_2698264 : Nat := 4983230072969 + 3 ^ 40 * 2698264 * 2
def baseEnd_2698264 : Nat := 307890303271852502975759

theorem tailTrace_2698264 : CollatzResearch.WordTrace tailWord_2698264 prefixEnd_2698264 307890303271852502975759 := by
  unfold tailWord_2698264
  simp only [CollatzResearch.WordTrace]
  refine ⟨49206886548328914824006923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65609182064438553098675897 49206886548328914824006923)
  ·
    refine ⟨73810329822493372236010385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49206886548328914824006923 73810329822493372236010385)
    ·
      refine ⟨55357747366870029177007789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73810329822493372236010385 55357747366870029177007789)
      ·
        refine ⟨20759155262576260941377921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55357747366870029177007789 20759155262576260941377921)
        ·
          refine ⟨15569366446932195706033441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20759155262576260941377921 15569366446932195706033441)
          ·
            refine ⟨11677024835199146779525081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15569366446932195706033441 11677024835199146779525081)
            ·
              refine ⟨8757768626399360084643811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11677024835199146779525081 8757768626399360084643811)
              ·
                refine ⟨13136652939599040126965717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8757768626399360084643811 13136652939599040126965717)
                ·
                  refine ⟨307890303271852502975759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13136652939599040126965717 307890303271852502975759)
                  ·
                    rfl

theorem cell22_2698264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 7].length) (baseStart_2698264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698264 prefixEnd_2698264 := by exact prefixLift 2698264
  have htrace : WordTrace (prefixWord ++ tailWord_2698264) baseStart_2698264 baseEnd_2698264 := by
    simpa [prefixWord, tailWord_2698264, baseEnd_2698264] using wordTrace_append hprefix tailTrace_2698264
  have hstable : (prefixWord ++ tailWord_2698264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698264).length < 2 ^ (prefixWord ++ tailWord_2698264).sum := by decide
  have hdescent : baseEnd_2698264 < baseStart_2698264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698339 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 1, 6]
def baseStart_2698339 : Nat := 118140960795 + 2698339 * 2 ^ 59
def prefixEnd_2698339 : Nat := 4983230072969 + 3 ^ 40 * 2698339 * 2
def baseEnd_2698339 : Nat := 923696583848282313302047

theorem tailTrace_2698339 : CollatzResearch.WordTrace tailWord_2698339 prefixEnd_2698339 923696583848282313302047 := by
  unfold tailWord_2698339
  simp only [CollatzResearch.WordTrace]
  refine ⟨98416508571386117456994071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65611005714257411637996047 98416508571386117456994071)
  ·
    refine ⟨147624762857079176185491107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98416508571386117456994071 147624762857079176185491107)
    ·
      refine ⟨221437144285618764278236661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147624762857079176185491107 221437144285618764278236661)
      ·
        refine ⟨20759732276776759151084687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 221437144285618764278236661 20759732276776759151084687)
        ·
          refine ⟨31139598415165138726627031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20759732276776759151084687 31139598415165138726627031)
          ·
            refine ⟨46709397622747708089940547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31139598415165138726627031 46709397622747708089940547)
            ·
              refine ⟨70064096434121562134910821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46709397622747708089940547 70064096434121562134910821)
              ·
                refine ⟨13137018081397792900295779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70064096434121562134910821 13137018081397792900295779)
                ·
                  refine ⟨19705527122096689350443669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13137018081397792900295779 19705527122096689350443669)
                  ·
                    refine ⟨923696583848282313302047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19705527122096689350443669 923696583848282313302047)
                    ·
                      rfl

theorem cell22_2698339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 6].length) (baseStart_2698339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698339 prefixEnd_2698339 := by exact prefixLift 2698339
  have htrace : WordTrace (prefixWord ++ tailWord_2698339) baseStart_2698339 baseEnd_2698339 := by
    simpa [prefixWord, tailWord_2698339, baseEnd_2698339] using wordTrace_append hprefix tailTrace_2698339
  have hstable : (prefixWord ++ tailWord_2698339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698339).length < 2 ^ (prefixWord ++ tailWord_2698339).sum := by decide
  have hdescent : baseEnd_2698339 < baseStart_2698339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698341 : List Nat := [1, 3, 1, 3, 2, 1, 4, 1, 1, 5]
def baseStart_2698341 : Nat := 118140960795 + 2698341 * 2 ^ 59
def prefixEnd_2698341 : Nat := 4983230072969 + 3 ^ 40 * 2698341 * 2
def baseEnd_2698341 : Nat := 923697268489154974752041

theorem tailTrace_2698341 : CollatzResearch.WordTrace tailWord_2698341 prefixEnd_2698341 923697268489154974752041 := by
  unfold tailWord_2698341
  simp only [CollatzResearch.WordTrace]
  refine ⟨98416581517378871798566877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65611054344919247865711251 98416581517378871798566877)
  ·
    refine ⟨36906218069017076924462579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98416581517378871798566877 36906218069017076924462579)
    ·
      refine ⟨55359327103525615386693869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36906218069017076924462579 55359327103525615386693869)
      ·
        refine ⟨20759747663822105770010201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55359327103525615386693869 20759747663822105770010201)
        ·
          refine ⟨15569810747866579327507651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20759747663822105770010201 15569810747866579327507651)
          ·
            refine ⟨23354716121799868991261477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15569810747866579327507651 23354716121799868991261477)
            ·
              refine ⟨4379009272837475435861527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23354716121799868991261477 4379009272837475435861527)
              ·
                refine ⟨6568513909256213153792291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4379009272837475435861527 6568513909256213153792291)
                ·
                  refine ⟨9852770863884319730688437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6568513909256213153792291 9852770863884319730688437)
                  ·
                    refine ⟨923697268489154974752041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9852770863884319730688437 923697268489154974752041)
                    ·
                      rfl

theorem cell22_2698341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_2698341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698341 prefixEnd_2698341 := by exact prefixLift 2698341
  have htrace : WordTrace (prefixWord ++ tailWord_2698341) baseStart_2698341 baseEnd_2698341 := by
    simpa [prefixWord, tailWord_2698341, baseEnd_2698341] using wordTrace_append hprefix tailTrace_2698341
  have hstable : (prefixWord ++ tailWord_2698341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698341).length < 2 ^ (prefixWord ++ tailWord_2698341).sum := by decide
  have hdescent : baseEnd_2698341 < baseStart_2698341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698358 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_2698358 : Nat := 118140960795 + 2698358 * 2 ^ 59
def prefixEnd_2698358 : Nat := 4983230072969 + 3 ^ 40 * 2698358 * 2
def baseEnd_2698358 : Nat := 923703087936572597076989

theorem tailTrace_2698358 : CollatzResearch.WordTrace tailWord_2698358 prefixEnd_2698358 923703087936572597076989 := by
  unfold tailWord_2698358
  simp only [CollatzResearch.WordTrace]
  refine ⟨6151075097394830231370983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65611467705544855801290485 6151075097394830231370983)
  ·
    refine ⟨9226612646092245347056475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6151075097394830231370983 9226612646092245347056475)
    ·
      refine ⟨13839918969138368020584713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9226612646092245347056475 13839918969138368020584713)
      ·
        refine ⟨10379939226853776015438535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13839918969138368020584713 10379939226853776015438535)
        ·
          refine ⟨15569908840280664023157803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10379939226853776015438535 15569908840280664023157803)
          ·
            refine ⟨23354863260420996034736705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15569908840280664023157803 23354863260420996034736705)
            ·
              refine ⟨17516147445315747026052529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23354863260420996034736705 17516147445315747026052529)
              ·
                refine ⟨13137110583986810269539397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17516147445315747026052529 13137110583986810269539397)
                ·
                  refine ⟨2463208234497526925538637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13137110583986810269539397 2463208234497526925538637)
                  ·
                    refine ⟨923703087936572597076989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2463208234497526925538637 923703087936572597076989)
                    ·
                      rfl

theorem cell22_2698358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_2698358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698358 prefixEnd_2698358 := by exact prefixLift 2698358
  have htrace : WordTrace (prefixWord ++ tailWord_2698358) baseStart_2698358 baseEnd_2698358 := by
    simpa [prefixWord, tailWord_2698358, baseEnd_2698358] using wordTrace_append hprefix tailTrace_2698358
  have hstable : (prefixWord ++ tailWord_2698358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698358).length < 2 ^ (prefixWord ++ tailWord_2698358).sum := by decide
  have hdescent : baseEnd_2698358 < baseStart_2698358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698384 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 2, 6]
def baseStart_2698384 : Nat := 118140960795 + 2698384 * 2 ^ 59
def prefixEnd_2698384 : Nat := 4983230072969 + 3 ^ 40 * 2698384 * 2
def baseEnd_2698384 : Nat := 923711988267917195926909

theorem tailTrace_2698384 : CollatzResearch.WordTrace tailWord_2698384 prefixEnd_2698384 923711988267917195926909 := by
  unfold tailWord_2698384
  simp only [CollatzResearch.WordTrace]
  refine ⟨49209074928111545071191103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65612099904148726761588137 49209074928111545071191103)
  ·
    refine ⟨73813612392167317606786655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49209074928111545071191103 73813612392167317606786655)
    ·
      refine ⟨110720418588250976410179983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73813612392167317606786655 110720418588250976410179983)
      ·
        refine ⟨166080627882376464615269975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110720418588250976410179983 166080627882376464615269975)
        ·
          refine ⟨249120941823564696922904963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166080627882376464615269975 249120941823564696922904963)
          ·
            refine ⟨373681412735347045384357445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249120941823564696922904963 373681412735347045384357445)
            ·
              refine ⟨70065264887877571009567021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 373681412735347045384357445 70065264887877571009567021)
              ·
                refine ⟨26274474332954089128587633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70065264887877571009567021 26274474332954089128587633)
                ·
                  refine ⟨19705855749715566846440725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26274474332954089128587633 19705855749715566846440725)
                  ·
                    refine ⟨923711988267917195926909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19705855749715566846440725 923711988267917195926909)
                    ·
                      rfl

theorem cell22_2698384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_2698384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698384 prefixEnd_2698384 := by exact prefixLift 2698384
  have htrace : WordTrace (prefixWord ++ tailWord_2698384) baseStart_2698384 baseEnd_2698384 := by
    simpa [prefixWord, tailWord_2698384, baseEnd_2698384] using wordTrace_append hprefix tailTrace_2698384
  have hstable : (prefixWord ++ tailWord_2698384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698384).length < 2 ^ (prefixWord ++ tailWord_2698384).sum := by decide
  have hdescent : baseEnd_2698384 < baseStart_2698384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698422 : List Nat := [5, 1, 3, 2, 2, 1, 8]
def baseStart_2698422 : Nat := 118140960795 + 2698422 * 2 ^ 59
def prefixEnd_2698422 : Nat := 4983230072969 + 3 ^ 40 * 2698422 * 2
def baseEnd_2698422 : Nat := 34212036905351769017659

theorem tailTrace_2698422 : CollatzResearch.WordTrace tailWord_2698422 prefixEnd_2698422 34212036905351769017659 := by
  unfold tailWord_2698422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6151220989380338914516595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65613023886723615088177013 6151220989380338914516595)
  ·
    refine ⟨9226831484070508371774893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6151220989380338914516595 9226831484070508371774893)
    ·
      refine ⟨3460061806526440639415585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9226831484070508371774893 3460061806526440639415585)
      ·
        refine ⟨2595046354894830479561689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3460061806526440639415585 2595046354894830479561689)
        ·
          refine ⟨1946284766171122859671267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2595046354894830479561689 1946284766171122859671267)
          ·
            refine ⟨2919427149256684289506901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946284766171122859671267 2919427149256684289506901)
            ·
              refine ⟨34212036905351769017659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2919427149256684289506901 34212036905351769017659)
              ·
                rfl

theorem cell22_2698422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 8].length) (baseStart_2698422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698422 prefixEnd_2698422 := by exact prefixLift 2698422
  have htrace : WordTrace (prefixWord ++ tailWord_2698422) baseStart_2698422 baseEnd_2698422 := by
    simpa [prefixWord, tailWord_2698422, baseEnd_2698422] using wordTrace_append hprefix tailTrace_2698422
  have hstable : (prefixWord ++ tailWord_2698422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698422).length < 2 ^ (prefixWord ++ tailWord_2698422).sum := by decide
  have hdescent : baseEnd_2698422 < baseStart_2698422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698433 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 7]
def baseStart_2698433 : Nat := 118140960795 + 2698433 * 2 ^ 59
def prefixEnd_2698433 : Nat := 4983230072969 + 3 ^ 40 * 2698433 * 2
def baseEnd_2698433 : Nat := 307909587323099133817253

theorem tailTrace_2698433 : CollatzResearch.WordTrace tailWord_2698433 prefixEnd_2698433 307909587323099133817253 := by
  unfold tailWord_2698433
  simp only [CollatzResearch.WordTrace]
  refine ⟨98419937033045571510915953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65613291355363714340610635 98419937033045571510915953)
  ·
    refine ⟨73814952774784178633186965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98419937033045571510915953 73814952774784178633186965)
    ·
      refine ⟨3460075911318008373430639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73814952774784178633186965 3460075911318008373430639)
      ·
        refine ⟨5190113866977012560145959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3460075911318008373430639 5190113866977012560145959)
        ·
          refine ⟨7785170800465518840218939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5190113866977012560145959 7785170800465518840218939)
          ·
            refine ⟨11677756200698278260328409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7785170800465518840218939 11677756200698278260328409)
            ·
              refine ⟨8758317150523708695246307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11677756200698278260328409 8758317150523708695246307)
              ·
                refine ⟨13137475725785563042869461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8758317150523708695246307 13137475725785563042869461)
                ·
                  refine ⟨307909587323099133817253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13137475725785563042869461 307909587323099133817253)
                  ·
                    rfl

theorem cell22_2698433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 7].length) (baseStart_2698433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698433 prefixEnd_2698433 := by exact prefixLift 2698433
  have htrace : WordTrace (prefixWord ++ tailWord_2698433) baseStart_2698433 baseEnd_2698433 := by
    simpa [prefixWord, tailWord_2698433, baseEnd_2698433] using wordTrace_append hprefix tailTrace_2698433
  have hstable : (prefixWord ++ tailWord_2698433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698433).length < 2 ^ (prefixWord ++ tailWord_2698433).sum := by decide
  have hdescent : baseEnd_2698433 < baseStart_2698433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698463 : List Nat := [1, 1, 2, 3, 2, 1, 5, 2, 1, 4]
def baseStart_2698463 : Nat := 118140960795 + 2698463 * 2 ^ 59
def prefixEnd_2698463 : Nat := 4983230072969 + 3 ^ 40 * 2698463 * 2
def baseEnd_2698463 : Nat := 923739031582387323201667

theorem tailTrace_2698463 : CollatzResearch.WordTrace tailWord_2698463 prefixEnd_2698463 923739031582387323201667 := by
  unfold tailWord_2698463
  simp only [CollatzResearch.WordTrace]
  refine ⟨98421031222936886634508043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65614020815291257756338695 98421031222936886634508043)
  ·
    refine ⟨147631546834405329951762065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98421031222936886634508043 147631546834405329951762065)
    ·
      refine ⟨110723660125803997463821549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147631546834405329951762065 110723660125803997463821549)
      ·
        refine ⟨41521372547176499048933081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110723660125803997463821549 41521372547176499048933081)
        ·
          refine ⟨31141029410382374286699811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41521372547176499048933081 31141029410382374286699811)
          ·
            refine ⟨46711544115573561430049717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31141029410382374286699811 46711544115573561430049717)
            ·
              refine ⟨4379207260835021384067161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46711544115573561430049717 4379207260835021384067161)
              ·
                refine ⟨3284405445626266038050371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4379207260835021384067161 3284405445626266038050371)
                ·
                  refine ⟨4926608168439399057075557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3284405445626266038050371 4926608168439399057075557)
                  ·
                    refine ⟨923739031582387323201667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4926608168439399057075557 923739031582387323201667)
                    ·
                      rfl

theorem cell22_2698463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 4].length) (baseStart_2698463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698463 prefixEnd_2698463 := by exact prefixLift 2698463
  have htrace : WordTrace (prefixWord ++ tailWord_2698463) baseStart_2698463 baseEnd_2698463 := by
    simpa [prefixWord, tailWord_2698463, baseEnd_2698463] using wordTrace_append hprefix tailTrace_2698463
  have hstable : (prefixWord ++ tailWord_2698463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698463).length < 2 ^ (prefixWord ++ tailWord_2698463).sum := by decide
  have hdescent : baseEnd_2698463 < baseStart_2698463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698476 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 3, 5]
def baseStart_2698476 : Nat := 118140960795 + 2698476 * 2 ^ 59
def prefixEnd_2698476 : Nat := 4983230072969 + 3 ^ 40 * 2698476 * 2
def baseEnd_2698476 : Nat := 923743481748059622626627

theorem tailTrace_2698476 : CollatzResearch.WordTrace tailWord_2698476 prefixEnd_2698476 923743481748059622626627 := by
  unfold tailWord_2698476
  simp only [CollatzResearch.WordTrace]
  refine ⟨49210752685944894927365641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65614336914593193236487521 49210752685944894927365641)
  ·
    refine ⟨36908064514458671195524231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49210752685944894927365641 36908064514458671195524231)
    ·
      refine ⟨55362096771688006793286347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36908064514458671195524231 55362096771688006793286347)
      ·
        refine ⟨83043145157532010189929521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55362096771688006793286347 83043145157532010189929521)
        ·
          refine ⟨62282358868149007642447141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83043145157532010189929521 62282358868149007642447141)
          ·
            refine ⟨11677942287777938932958839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62282358868149007642447141 11677942287777938932958839)
            ·
              refine ⟨17516913431666908399438259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11677942287777938932958839 17516913431666908399438259)
              ·
                refine ⟨26275370147500362599157389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17516913431666908399438259 26275370147500362599157389)
                ·
                  refine ⟨9853263805312635974684021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26275370147500362599157389 9853263805312635974684021)
                  ·
                    refine ⟨923743481748059622626627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9853263805312635974684021 923743481748059622626627)
                    ·
                      rfl

theorem cell22_2698476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_2698476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698476 prefixEnd_2698476 := by exact prefixLift 2698476
  have htrace : WordTrace (prefixWord ++ tailWord_2698476) baseStart_2698476 baseEnd_2698476 := by
    simpa [prefixWord, tailWord_2698476, baseEnd_2698476] using wordTrace_append hprefix tailTrace_2698476
  have hstable : (prefixWord ++ tailWord_2698476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698476).length < 2 ^ (prefixWord ++ tailWord_2698476).sum := by decide
  have hdescent : baseEnd_2698476 < baseStart_2698476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698484 : List Nat := [2, 6, 1, 2, 1, 1, 2, 2, 5]
def baseStart_2698484 : Nat := 118140960795 + 2698484 * 2 ^ 59
def prefixEnd_2698484 : Nat := 4983230072969 + 3 ^ 40 * 2698484 * 2
def baseEnd_2698484 : Nat := 307915406770516756142201

theorem tailTrace_2698484 : CollatzResearch.WordTrace tailWord_2698484 prefixEnd_2698484 307915406770516756142201 := by
  unfold tailWord_2698484
  simp only [CollatzResearch.WordTrace]
  refine ⟨49210898577930403610511253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65614531437240538147348337 49210898577930403610511253)
  ·
    refine ⟨2306760870840487669242715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49210898577930403610511253 2306760870840487669242715)
    ·
      refine ⟨3460141306260731503864073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2306760870840487669242715 3460141306260731503864073)
      ·
        refine ⟨2595105979695548627898055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3460141306260731503864073 2595105979695548627898055)
        ·
          refine ⟨3892658969543322941847083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2595105979695548627898055 3892658969543322941847083)
          ·
            refine ⟨5838988454314984412770625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3892658969543322941847083 5838988454314984412770625)
            ·
              refine ⟨4379241340736238309577969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5838988454314984412770625 4379241340736238309577969)
              ·
                refine ⟨3284431005552178732183477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4379241340736238309577969 3284431005552178732183477)
                ·
                  refine ⟨307915406770516756142201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3284431005552178732183477 307915406770516756142201)
                  ·
                    rfl

theorem cell22_2698484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_2698484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698484 prefixEnd_2698484 := by exact prefixLift 2698484
  have htrace : WordTrace (prefixWord ++ tailWord_2698484) baseStart_2698484 baseEnd_2698484 := by
    simpa [prefixWord, tailWord_2698484, baseEnd_2698484] using wordTrace_append hprefix tailTrace_2698484
  have hstable : (prefixWord ++ tailWord_2698484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698484).length < 2 ^ (prefixWord ++ tailWord_2698484).sum := by decide
  have hdescent : baseEnd_2698484 < baseStart_2698484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698495 : List Nat := [1, 1, 2, 2, 1, 5, 4, 2, 4]
def baseStart_2698495 : Nat := 118140960795 + 2698495 * 2 ^ 59
def prefixEnd_2698495 : Nat := 4983230072969 + 3 ^ 40 * 2698495 * 2
def baseEnd_2698495 : Nat := 307916661945449968800523

theorem tailTrace_2698495 : CollatzResearch.WordTrace tailWord_2698495 prefixEnd_2698495 307916661945449968800523 := by
  unfold tailWord_2698495
  simp only [CollatzResearch.WordTrace]
  refine ⟨98422198358820956099672939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65614798905880637399781959 98422198358820956099672939)
  ·
    refine ⟨147633297538231434149509409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98422198358820956099672939 147633297538231434149509409)
    ·
      refine ⟨110724973153673575612132057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147633297538231434149509409 110724973153673575612132057)
      ·
        refine ⟨83043729865255181709099043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110724973153673575612132057 83043729865255181709099043)
        ·
          refine ⟨124565594797882772563648565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83043729865255181709099043 124565594797882772563648565)
          ·
            refine ⟨11678024512301509927842053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124565594797882772563648565 11678024512301509927842053)
            ·
              refine ⟨2189629596056533111470385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11678024512301509927842053 2189629596056533111470385)
              ·
                refine ⟨1642222197042399833602789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2189629596056533111470385 1642222197042399833602789)
                ·
                  refine ⟨307916661945449968800523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1642222197042399833602789 307916661945449968800523)
                  ·
                    rfl

theorem cell22_2698495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 4].length) (baseStart_2698495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698495 prefixEnd_2698495 := by exact prefixLift 2698495
  have htrace : WordTrace (prefixWord ++ tailWord_2698495) baseStart_2698495 baseEnd_2698495 := by
    simpa [prefixWord, tailWord_2698495, baseEnd_2698495] using wordTrace_append hprefix tailTrace_2698495
  have hstable : (prefixWord ++ tailWord_2698495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698495).length < 2 ^ (prefixWord ++ tailWord_2698495).sum := by decide
  have hdescent : baseEnd_2698495 < baseStart_2698495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698510 : List Nat := [4, 1, 1, 2, 1, 3, 2, 3, 2, 3]
def baseStart_2698510 : Nat := 118140960795 + 2698510 * 2 ^ 59
def prefixEnd_2698510 : Nat := 4983230072969 + 3 ^ 40 * 2698510 * 2
def baseEnd_2698510 : Nat := 923755120642894867276523

theorem tailTrace_2698510 : CollatzResearch.WordTrace tailWord_2698510 prefixEnd_2698510 923755120642894867276523 := by
  unfold tailWord_2698510
  simp only [CollatzResearch.WordTrace]
  refine ⟨12302843181720826707683623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65615163635844409107645989 12302843181720826707683623)
  ·
    refine ⟨18454264772581240061525435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12302843181720826707683623 18454264772581240061525435)
    ·
      refine ⟨27681397158871860092288153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18454264772581240061525435 27681397158871860092288153)
      ·
        refine ⟨20761047869153895069216115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27681397158871860092288153 20761047869153895069216115)
        ·
          refine ⟨31141571803730842603824173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20761047869153895069216115 31141571803730842603824173)
          ·
            refine ⟨11678089426399065976434065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31141571803730842603824173 11678089426399065976434065)
            ·
              refine ⟨8758567069799299482325549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11678089426399065976434065 8758567069799299482325549)
              ·
                refine ⟨3284462651174737305872081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8758567069799299482325549 3284462651174737305872081)
                ·
                  refine ⟨2463346988381052979404061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3284462651174737305872081 2463346988381052979404061)
                  ·
                    refine ⟨923755120642894867276523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2463346988381052979404061 923755120642894867276523)
                    ·
                      rfl

theorem cell22_2698510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_2698510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698510 prefixEnd_2698510 := by exact prefixLift 2698510
  have htrace : WordTrace (prefixWord ++ tailWord_2698510) baseStart_2698510 baseEnd_2698510 := by
    simpa [prefixWord, tailWord_2698510, baseEnd_2698510] using wordTrace_append hprefix tailTrace_2698510
  have hstable : (prefixWord ++ tailWord_2698510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698510).length < 2 ^ (prefixWord ++ tailWord_2698510).sum := by decide
  have hdescent : baseEnd_2698510 < baseStart_2698510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698525 : List Nat := [1, 4, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_2698525 : Nat := 118140960795 + 2698525 * 2 ^ 59
def prefixEnd_2698525 : Nat := 4983230072969 + 3 ^ 40 * 2698525 * 2
def baseEnd_2698525 : Nat := 923760255449439828151477

theorem tailTrace_2698525 : CollatzResearch.WordTrace tailWord_2698525 prefixEnd_2698525 923760255449439828151477 := by
  unfold tailWord_2698525
  simp only [CollatzResearch.WordTrace]
  refine ⟨98423292548712271223265029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65615528365808180815510019 98423292548712271223265029)
  ·
    refine ⟨18454367352883550854362193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98423292548712271223265029 18454367352883550854362193)
    ·
      refine ⟨13840775514662663140771645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18454367352883550854362193 13840775514662663140771645)
      ·
        refine ⟨5190290817998498677789367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13840775514662663140771645 5190290817998498677789367)
        ·
          refine ⟨7785436226997748016684051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5190290817998498677789367 7785436226997748016684051)
          ·
            refine ⟨11678154340496622025026077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7785436226997748016684051 11678154340496622025026077)
            ·
              refine ⟨4379307877686233259384779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11678154340496622025026077 4379307877686233259384779)
              ·
                refine ⟨6568961816529349889077169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4379307877686233259384779 6568961816529349889077169)
                ·
                  refine ⟨4926721362397012416807877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6568961816529349889077169 4926721362397012416807877)
                  ·
                    refine ⟨923760255449439828151477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4926721362397012416807877 923760255449439828151477)
                    ·
                      rfl

theorem cell22_2698525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_2698525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698525 prefixEnd_2698525 := by exact prefixLift 2698525
  have htrace : WordTrace (prefixWord ++ tailWord_2698525) baseStart_2698525 baseEnd_2698525 := by
    simpa [prefixWord, tailWord_2698525, baseEnd_2698525] using wordTrace_append hprefix tailTrace_2698525
  have hstable : (prefixWord ++ tailWord_2698525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698525).length < 2 ^ (prefixWord ++ tailWord_2698525).sum := by decide
  have hdescent : baseEnd_2698525 < baseStart_2698525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698606 : List Nat := [4, 1, 2, 4, 2, 1, 1, 1, 3, 3]
def baseStart_2698606 : Nat := 118140960795 + 2698606 * 2 ^ 59
def prefixEnd_2698606 : Nat := 4983230072969 + 3 ^ 40 * 2698606 * 2
def baseEnd_2698606 : Nat := 923787983404782616876229

theorem tailTrace_2698606 : CollatzResearch.WordTrace tailWord_2698606 prefixEnd_2698606 923787983404782616876229 := by
  unfold tailWord_2698606
  simp only [CollatzResearch.WordTrace]
  refine ⟨12303280857677352757120459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65617497907612548037975781 12303280857677352757120459)
  ·
    refine ⟨18454921286516029135680689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12303280857677352757120459 18454921286516029135680689)
    ·
      refine ⟨13841190964887021851760517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18454921286516029135680689 13841190964887021851760517)
      ·
        refine ⟨2595223305916316597205097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13841190964887021851760517 2595223305916316597205097)
        ·
          refine ⟨1946417479437237447903823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2595223305916316597205097 1946417479437237447903823)
          ·
            refine ⟨2919626219155856171855735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946417479437237447903823 2919626219155856171855735)
            ·
              refine ⟨4379439328733784257783603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2919626219155856171855735 4379439328733784257783603)
              ·
                refine ⟨6569158993100676386675405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4379439328733784257783603 6569158993100676386675405)
                ·
                  refine ⟨2463434622412753645003277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6569158993100676386675405 2463434622412753645003277)
                  ·
                    refine ⟨923787983404782616876229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2463434622412753645003277 923787983404782616876229)
                    ·
                      rfl

theorem cell22_2698606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_2698606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698606 prefixEnd_2698606 := by exact prefixLift 2698606
  have htrace : WordTrace (prefixWord ++ tailWord_2698606) baseStart_2698606 baseEnd_2698606 := by
    simpa [prefixWord, tailWord_2698606, baseEnd_2698606] using wordTrace_append hprefix tailTrace_2698606
  have hstable : (prefixWord ++ tailWord_2698606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698606).length < 2 ^ (prefixWord ++ tailWord_2698606).sum := by decide
  have hdescent : baseEnd_2698606 < baseStart_2698606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698611 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 2, 9]
def baseStart_2698611 : Nat := 118140960795 + 2698611 * 2 ^ 59
def prefixEnd_2698611 : Nat := 4983230072969 + 3 ^ 40 * 2698611 * 2
def baseEnd_2698611 : Nat := 923789695006964270501213

theorem tailTrace_2698611 : CollatzResearch.WordTrace tailWord_2698611 prefixEnd_2698611 923789695006964270501213 := by
  unfold tailWord_2698611
  simp only [CollatzResearch.WordTrace]
  refine ⟨98426429226400707910895687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65617619484267138607263791 98426429226400707910895687)
  ·
    refine ⟨147639643839601061866343531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98426429226400707910895687 147639643839601061866343531)
    ·
      refine ⟨221459465759401592799515297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147639643839601061866343531 221459465759401592799515297)
      ·
        refine ⟨166094599319551194599636473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221459465759401592799515297 166094599319551194599636473)
        ·
          refine ⟨124570949489663395949727355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166094599319551194599636473 124570949489663395949727355)
          ·
            refine ⟨186856424234495093924591033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124570949489663395949727355 186856424234495093924591033)
            ·
              refine ⟨140142318175871320443443275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186856424234495093924591033 140142318175871320443443275)
              ·
                refine ⟨210213477263806980665164913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140142318175871320443443275 210213477263806980665164913)
                ·
                  refine ⟨157660107947855235498873685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210213477263806980665164913 157660107947855235498873685)
                  ·
                    refine ⟨923789695006964270501213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 157660107947855235498873685 923789695006964270501213)
                    ·
                      rfl

theorem cell22_2698611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 9].length) (baseStart_2698611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698611 prefixEnd_2698611 := by exact prefixLift 2698611
  have htrace : WordTrace (prefixWord ++ tailWord_2698611) baseStart_2698611 baseEnd_2698611 := by
    simpa [prefixWord, tailWord_2698611, baseEnd_2698611] using wordTrace_append hprefix tailTrace_2698611
  have hstable : (prefixWord ++ tailWord_2698611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698611).length < 2 ^ (prefixWord ++ tailWord_2698611).sum := by decide
  have hdescent : baseEnd_2698611 < baseStart_2698611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698632 : List Nat := [2, 1, 3, 3, 1, 4, 1, 2, 1, 4]
def baseStart_2698632 : Nat := 118140960795 + 2698632 * 2 ^ 59
def prefixEnd_2698632 : Nat := 4983230072969 + 3 ^ 40 * 2698632 * 2
def baseEnd_2698632 : Nat := 923796883736127215726149

theorem tailTrace_2698632 : CollatzResearch.WordTrace tailWord_2698632 prefixEnd_2698632 923796883736127215726149 := by
  unfold tailWord_2698632
  simp only [CollatzResearch.WordTrace]
  refine ⟨49213597579662314248705075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65618130106216418998273433 49213597579662314248705075)
  ·
    refine ⟨73820396369493471373057613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49213597579662314248705075 73820396369493471373057613)
    ·
      refine ⟨27682648638560051764896605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73820396369493471373057613 27682648638560051764896605)
      ·
        refine ⟨10380993239460019411836227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27682648638560051764896605 10380993239460019411836227)
        ·
          refine ⟨15571489859190029117754341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10380993239460019411836227 15571489859190029117754341)
          ·
            refine ⟨2919654348598130459578939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15571489859190029117754341 2919654348598130459578939)
            ·
              refine ⟨4379481522897195689368409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2919654348598130459578939 4379481522897195689368409)
              ·
                refine ⟨3284611142172896767026307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4379481522897195689368409 3284611142172896767026307)
                ·
                  refine ⟨4926916713259345150539461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3284611142172896767026307 4926916713259345150539461)
                  ·
                    refine ⟨923796883736127215726149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4926916713259345150539461 923796883736127215726149)
                    ·
                      rfl

theorem cell22_2698632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_2698632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698632 prefixEnd_2698632 := by exact prefixLift 2698632
  have htrace : WordTrace (prefixWord ++ tailWord_2698632) baseStart_2698632 baseEnd_2698632 := by
    simpa [prefixWord, tailWord_2698632, baseEnd_2698632] using wordTrace_append hprefix tailTrace_2698632
  have hstable : (prefixWord ++ tailWord_2698632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698632).length < 2 ^ (prefixWord ++ tailWord_2698632).sum := by decide
  have hdescent : baseEnd_2698632 < baseStart_2698632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698658 : List Nat := [3, 3, 1, 2, 1, 12]
def baseStart_2698658 : Nat := 118140960795 + 2698658 * 2 ^ 59
def prefixEnd_2698658 : Nat := 4983230072969 + 3 ^ 40 * 2698658 * 2
def baseEnd_2698658 : Nat := 11405009679845331044149

theorem tailTrace_2698658 : CollatzResearch.WordTrace tailWord_2698658 prefixEnd_2698658 11405009679845331044149 := by
  unfold tailWord_2698658
  simp only [CollatzResearch.WordTrace]
  refine ⟨24607035864307608734464157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65618762304820289958571085 24607035864307608734464157)
  ·
    refine ⟨9227638449115353275424059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24607035864307608734464157 9227638449115353275424059)
    ·
      refine ⟨13841457673673029913136089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9227638449115353275424059 13841457673673029913136089)
      ·
        refine ⟨10381093255254772434852067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13841457673673029913136089 10381093255254772434852067)
        ·
          refine ⟨15571639882882158652278101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10381093255254772434852067 15571639882882158652278101)
          ·
            refine ⟨11405009679845331044149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15571639882882158652278101 11405009679845331044149)
            ·
              rfl

theorem cell22_2698658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 12].length) (baseStart_2698658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698658 prefixEnd_2698658 := by exact prefixLift 2698658
  have htrace : WordTrace (prefixWord ++ tailWord_2698658) baseStart_2698658 baseEnd_2698658 := by
    simpa [prefixWord, tailWord_2698658, baseEnd_2698658] using wordTrace_append hprefix tailTrace_2698658
  have hstable : (prefixWord ++ tailWord_2698658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698658).length < 2 ^ (prefixWord ++ tailWord_2698658).sum := by decide
  have hdescent : baseEnd_2698658 < baseStart_2698658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698664 : List Nat := [2, 1, 6, 1, 2, 1, 1, 4, 4]
def baseStart_2698664 : Nat := 118140960795 + 2698664 * 2 ^ 59
def prefixEnd_2698664 : Nat := 4983230072969 + 3 ^ 40 * 2698664 * 2
def baseEnd_2698664 : Nat := 307935945996696599642017

theorem tailTrace_2698664 : CollatzResearch.WordTrace tailWord_2698664 prefixEnd_2698664 307935945996696599642017 := by
  unfold tailWord_2698664
  simp only [CollatzResearch.WordTrace]
  refine ⟨49214181147604348981287523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65618908196805798641716697 49214181147604348981287523)
  ·
    refine ⟨73821271721406523471931285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49214181147604348981287523 73821271721406523471931285)
    ·
      refine ⟨3460372111940930787746779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73821271721406523471931285 3460372111940930787746779)
      ·
        refine ⟨5190558167911396181620169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3460372111940930787746779 5190558167911396181620169)
        ·
          refine ⟨3892918625933547136215127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5190558167911396181620169 3892918625933547136215127)
          ·
            refine ⟨5839377938900320704322691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3892918625933547136215127 5839377938900320704322691)
            ·
              refine ⟨8759066908350481056484037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5839377938900320704322691 8759066908350481056484037)
              ·
                refine ⟨1642325045315715198090757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8759066908350481056484037 1642325045315715198090757)
                ·
                  refine ⟨307935945996696599642017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1642325045315715198090757 307935945996696599642017)
                  ·
                    rfl

theorem cell22_2698664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 4].length) (baseStart_2698664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698664 prefixEnd_2698664 := by exact prefixLift 2698664
  have htrace : WordTrace (prefixWord ++ tailWord_2698664) baseStart_2698664 baseEnd_2698664 := by
    simpa [prefixWord, tailWord_2698664, baseEnd_2698664] using wordTrace_append hprefix tailTrace_2698664
  have hstable : (prefixWord ++ tailWord_2698664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698664).length < 2 ^ (prefixWord ++ tailWord_2698664).sum := by decide
  have hdescent : baseEnd_2698664 < baseStart_2698664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698692 : List Nat := [2, 3, 3, 2, 1, 2, 3, 6]
def baseStart_2698692 : Nat := 118140960795 + 2698692 * 2 ^ 59
def prefixEnd_2698692 : Nat := 4983230072969 + 3 ^ 40 * 2698692 * 2
def baseEnd_2698692 : Nat := 102646380329145228802885

theorem tailTrace_2698692 : CollatzResearch.WordTrace tailWord_2698692 prefixEnd_2698692 102646380329145228802885 := by
  unfold tailWord_2698692
  simp only [CollatzResearch.WordTrace]
  refine ⟨49214691769553629372297165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65619589026071505829729553 49214691769553629372297165)
  ·
    refine ⟨18455509413582611014611437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49214691769553629372297165 18455509413582611014611437)
    ·
      refine ⟨6920816030093479130479289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18455509413582611014611437 6920816030093479130479289)
      ·
        refine ⟨5190612022570109347859467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6920816030093479130479289 5190612022570109347859467)
        ·
          refine ⟨7785918033855164021789201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5190612022570109347859467 7785918033855164021789201)
          ·
            refine ⟨5839438525391373016341901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7785918033855164021789201 5839438525391373016341901)
            ·
              refine ⟨2189789447021764881128213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5839438525391373016341901 2189789447021764881128213)
              ·
                refine ⟨102646380329145228802885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2189789447021764881128213 102646380329145228802885)
                ·
                  rfl

theorem cell22_2698692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 6].length) (baseStart_2698692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698692 prefixEnd_2698692 := by exact prefixLift 2698692
  have htrace : WordTrace (prefixWord ++ tailWord_2698692) baseStart_2698692 baseEnd_2698692 := by
    simpa [prefixWord, tailWord_2698692, baseEnd_2698692] using wordTrace_append hprefix tailTrace_2698692
  have hstable : (prefixWord ++ tailWord_2698692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698692).length < 2 ^ (prefixWord ++ tailWord_2698692).sum := by decide
  have hdescent : baseEnd_2698692 < baseStart_2698692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698737 : List Nat := [1, 2, 2, 2, 3, 3, 3, 1, 5]
def baseStart_2698737 : Nat := 118140960795 + 2698737 * 2 ^ 59
def prefixEnd_2698737 : Nat := 4983230072969 + 3 ^ 40 * 2698737 * 2
def baseEnd_2698737 : Nat := 307944275793980647283609

theorem tailTrace_2698737 : CollatzResearch.WordTrace tailWord_2698737 prefixEnd_2698737 307944275793980647283609 := by
  unfold tailWord_2698737
  simp only [CollatzResearch.WordTrace]
  refine ⟨98431024823944231429982465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65620683215962820953321643 98431024823944231429982465)
  ·
    refine ⟨73823268617958173572486849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98431024823944231429982465 73823268617958173572486849)
    ·
      refine ⟨55367451463468630179365137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73823268617958173572486849 55367451463468630179365137)
      ·
        refine ⟨41525588597601472634523853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55367451463468630179365137 41525588597601472634523853)
        ·
          refine ⟨15572095724100552237946445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41525588597601472634523853 15572095724100552237946445)
          ·
            refine ⟨5839535896537707089229917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15572095724100552237946445 5839535896537707089229917)
            ·
              refine ⟨2189825961201640158461219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5839535896537707089229917 2189825961201640158461219)
              ·
                refine ⟨3284738941802460237691829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2189825961201640158461219 3284738941802460237691829)
                ·
                  refine ⟨307944275793980647283609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3284738941802460237691829 307944275793980647283609)
                  ·
                    rfl

theorem cell22_2698737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 5].length) (baseStart_2698737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698737 prefixEnd_2698737 := by exact prefixLift 2698737
  have htrace : WordTrace (prefixWord ++ tailWord_2698737) baseStart_2698737 baseEnd_2698737 := by
    simpa [prefixWord, tailWord_2698737, baseEnd_2698737] using wordTrace_append hprefix tailTrace_2698737
  have hstable : (prefixWord ++ tailWord_2698737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698737).length < 2 ^ (prefixWord ++ tailWord_2698737).sum := by decide
  have hdescent : baseEnd_2698737 < baseStart_2698737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698960 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 2, 7]
def baseStart_2698960 : Nat := 118140960795 + 2698960 * 2 ^ 59
def prefixEnd_2698960 : Nat := 4983230072969 + 3 ^ 40 * 2698960 * 2
def baseEnd_2698960 : Nat := 923909164839243693525143

theorem tailTrace_2698960 : CollatzResearch.WordTrace tailWord_2698960 prefixEnd_2698960 923909164839243693525143 := by
  unfold tailWord_2698960
  simp only [CollatzResearch.WordTrace]
  refine ⟨49219579151068170257675167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65626105534757560343566889 49219579151068170257675167)
  ·
    refine ⟨73829368726602255386512751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49219579151068170257675167 73829368726602255386512751)
    ·
      refine ⟨110744053089903383079769127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73829368726602255386512751 110744053089903383079769127)
      ·
        refine ⟨166116079634855074619653691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110744053089903383079769127 166116079634855074619653691)
        ·
          refine ⟨249174119452282611929480537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166116079634855074619653691 249174119452282611929480537)
          ·
            refine ⟨186880589589211958947110403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249174119452282611929480537 186880589589211958947110403)
            ·
              refine ⟨280320884383817938420665605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186880589589211958947110403 280320884383817938420665605)
              ·
                refine ⟨52560165821965863453874801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 280320884383817938420665605 52560165821965863453874801)
                ·
                  refine ⟨39420124366474397590406101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52560165821965863453874801 39420124366474397590406101)
                  ·
                    refine ⟨923909164839243693525143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39420124366474397590406101 923909164839243693525143)
                    ·
                      rfl

theorem cell22_2698960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_2698960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698960 prefixEnd_2698960 := by exact prefixLift 2698960
  have htrace : WordTrace (prefixWord ++ tailWord_2698960) baseStart_2698960 baseEnd_2698960 := by
    simpa [prefixWord, tailWord_2698960, baseEnd_2698960] using wordTrace_append hprefix tailTrace_2698960
  have hstable : (prefixWord ++ tailWord_2698960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698960).length < 2 ^ (prefixWord ++ tailWord_2698960).sum := by decide
  have hdescent : baseEnd_2698960 < baseStart_2698960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698962 : List Nat := [3, 2, 2, 2, 2, 1, 1, 9]
def baseStart_2698962 : Nat := 118140960795 + 2698962 * 2 ^ 59
def prefixEnd_2698962 : Nat := 4983230072969 + 3 ^ 40 * 2698962 * 2
def baseEnd_2698962 : Nat := 102656649942235150552793

theorem tailTrace_2698962 : CollatzResearch.WordTrace tailWord_2698962 prefixEnd_2698962 102656649942235150552793 := by
  unfold tailWord_2698962
  simp only [CollatzResearch.WordTrace]
  refine ⟨24609807812032273714230785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65626154165419396571282093 24609807812032273714230785)
  ·
    refine ⟨18457355859024205285673089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24609807812032273714230785 18457355859024205285673089)
    ·
      refine ⟨13843016894268153964254817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18457355859024205285673089 13843016894268153964254817)
      ·
        refine ⟨10382262670701115473191113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13843016894268153964254817 10382262670701115473191113)
        ·
          refine ⟨7786697003025836604893335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10382262670701115473191113 7786697003025836604893335)
          ·
            refine ⟨11680045504538754907340003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7786697003025836604893335 11680045504538754907340003)
            ·
              refine ⟨17520068256808132361010005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11680045504538754907340003 17520068256808132361010005)
              ·
                refine ⟨102656649942235150552793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17520068256808132361010005 102656649942235150552793)
                ·
                  rfl

theorem cell22_2698962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 9].length) (baseStart_2698962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2698962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2698962 prefixEnd_2698962 := by exact prefixLift 2698962
  have htrace : WordTrace (prefixWord ++ tailWord_2698962) baseStart_2698962 baseEnd_2698962 := by
    simpa [prefixWord, tailWord_2698962, baseEnd_2698962] using wordTrace_append hprefix tailTrace_2698962
  have hstable : (prefixWord ++ tailWord_2698962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698962).length < 2 ^ (prefixWord ++ tailWord_2698962).sum := by decide
  have hdescent : baseEnd_2698962 < baseStart_2698962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699007 : List Nat := [1, 1, 2, 2, 1, 3, 3, 4, 5]
def baseStart_2699007 : Nat := 118140960795 + 2699007 * 2 ^ 59
def prefixEnd_2699007 : Nat := 4983230072969 + 3 ^ 40 * 2699007 * 2
def baseEnd_2699007 : Nat := 307975084633250412533333

theorem tailTrace_2699007 : CollatzResearch.WordTrace tailWord_2699007 prefixEnd_2699007 307975084633250412533333 := by
  unfold tailWord_2699007
  simp only [CollatzResearch.WordTrace]
  refine ⟨98440872532966067542311275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65627248355310711694874183 98440872532966067542311275)
  ·
    refine ⟨147661308799449101313466913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98440872532966067542311275 147661308799449101313466913)
    ·
      refine ⟨110745981599586825985100185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147661308799449101313466913 110745981599586825985100185)
      ·
        refine ⟨83059486199690119488825139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110745981599586825985100185 83059486199690119488825139)
        ·
          refine ⟨124589229299535179233237709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83059486199690119488825139 124589229299535179233237709)
          ·
            refine ⟨46720960987325692212464141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124589229299535179233237709 46720960987325692212464141)
            ·
              refine ⟨17520360370247134579674053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46720960987325692212464141 17520360370247134579674053)
              ·
                refine ⟨3285067569421337733688885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17520360370247134579674053 3285067569421337733688885)
                ·
                  refine ⟨307975084633250412533333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3285067569421337733688885 307975084633250412533333)
                  ·
                    rfl

theorem cell22_2699007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 5].length) (baseStart_2699007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699007 prefixEnd_2699007 := by exact prefixLift 2699007
  have htrace : WordTrace (prefixWord ++ tailWord_2699007) baseStart_2699007 baseEnd_2699007 := by
    simpa [prefixWord, tailWord_2699007, baseEnd_2699007] using wordTrace_append hprefix tailTrace_2699007
  have hstable : (prefixWord ++ tailWord_2699007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699007).length < 2 ^ (prefixWord ++ tailWord_2699007).sum := by decide
  have hdescent : baseEnd_2699007 < baseStart_2699007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699022 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_2699022 : Nat := 118140960795 + 2699022 * 2 ^ 59
def prefixEnd_2699022 : Nat := 4983230072969 + 3 ^ 40 * 2699022 * 2
def baseEnd_2699022 : Nat := 923930388706296198474953

theorem tailTrace_2699022 : CollatzResearch.WordTrace tailWord_2699022 prefixEnd_2699022 923930388706296198474953 := by
  unfold tailWord_2699022
  simp only [CollatzResearch.WordTrace]
  refine ⟨12305177453488965638013415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65627613085274483402738213 12305177453488965638013415)
  ·
    refine ⟨18457766180233448457020123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12305177453488965638013415 18457766180233448457020123)
    ·
      refine ⟨27686649270350172685530185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18457766180233448457020123 27686649270350172685530185)
      ·
        refine ⟨20764986952762629514147639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27686649270350172685530185 20764986952762629514147639)
        ·
          refine ⟨31147480429143944271221459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20764986952762629514147639 31147480429143944271221459)
          ·
            refine ⟨46721220643715916406832189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31147480429143944271221459 46721220643715916406832189)
            ·
              refine ⟨17520457741393468652562071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46721220643715916406832189 17520457741393468652562071)
              ·
                refine ⟨26280686612090202978843107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17520457741393468652562071 26280686612090202978843107)
                ·
                  refine ⟨39421029918135304468264661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26280686612090202978843107 39421029918135304468264661)
                  ·
                    refine ⟨923930388706296198474953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39421029918135304468264661 923930388706296198474953)
                    ·
                      rfl

theorem cell22_2699022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_2699022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699022 prefixEnd_2699022 := by exact prefixLift 2699022
  have htrace : WordTrace (prefixWord ++ tailWord_2699022) baseStart_2699022 baseEnd_2699022 := by
    simpa [prefixWord, tailWord_2699022, baseEnd_2699022] using wordTrace_append hprefix tailTrace_2699022
  have hstable : (prefixWord ++ tailWord_2699022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699022).length < 2 ^ (prefixWord ++ tailWord_2699022).sum := by decide
  have hdescent : baseEnd_2699022 < baseStart_2699022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699069 : List Nat := [1, 4, 1, 4, 1, 1, 1, 3, 6]
def baseStart_2699069 : Nat := 118140960795 + 2699069 * 2 ^ 59
def prefixEnd_2699069 : Nat := 4983230072969 + 3 ^ 40 * 2699069 * 2
def baseEnd_2699069 : Nat := 307982159255601247516603

theorem tailTrace_2699069 : CollatzResearch.WordTrace tailWord_2699069 prefixEnd_2699069 307982159255601247516603 := by
  unfold tailWord_2699069
  simp only [CollatzResearch.WordTrace]
  refine ⟨98443133858741452131068261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65628755905827634754045507 98443133858741452131068261)
  ·
    refine ⟨18458087598514022274575299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98443133858741452131068261 18458087598514022274575299)
    ·
      refine ⟨27687131397771033411862949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18458087598514022274575299 27687131397771033411862949)
      ·
        refine ⟨5191337137082068764724303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27687131397771033411862949 5191337137082068764724303)
        ·
          refine ⟨7787005705623103147086455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5191337137082068764724303 7787005705623103147086455)
          ·
            refine ⟨11680508558434654720629683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7787005705623103147086455 11680508558434654720629683)
            ·
              refine ⟨17520762837651982080944525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11680508558434654720629683 17520762837651982080944525)
              ·
                refine ⟨6570286064119493280354197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17520762837651982080944525 6570286064119493280354197)
                ·
                  refine ⟨307982159255601247516603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6570286064119493280354197 307982159255601247516603)
                  ·
                    rfl

theorem cell22_2699069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_2699069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699069 prefixEnd_2699069 := by exact prefixLift 2699069
  have htrace : WordTrace (prefixWord ++ tailWord_2699069) baseStart_2699069 baseEnd_2699069 := by
    simpa [prefixWord, tailWord_2699069, baseEnd_2699069] using wordTrace_append hprefix tailTrace_2699069
  have hstable : (prefixWord ++ tailWord_2699069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699069).length < 2 ^ (prefixWord ++ tailWord_2699069).sum := by decide
  have hdescent : baseEnd_2699069 < baseStart_2699069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699082 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 3, 6]
def baseStart_2699082 : Nat := 118140960795 + 2699082 * 2 ^ 59
def prefixEnd_2699082 : Nat := 4983230072969 + 3 ^ 40 * 2699082 * 2
def baseEnd_2699082 : Nat := 923950927932476041974769

theorem tailTrace_2699082 : CollatzResearch.WordTrace tailWord_2699082 prefixEnd_2699082 923950927932476041974769 := by
  unfold tailWord_2699082
  simp only [CollatzResearch.WordTrace]
  refine ⟨24610902001923588837822875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65629072005129570234194333 24610902001923588837822875)
  ·
    refine ⟨36916353002885383256734313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24610902001923588837822875 36916353002885383256734313)
    ·
      refine ⟨27687264752164037442550735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36916353002885383256734313 27687264752164037442550735)
      ·
        refine ⟨41530897128246056163826103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27687264752164037442550735 41530897128246056163826103)
        ·
          refine ⟨62296345692369084245739155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41530897128246056163826103 62296345692369084245739155)
          ·
            refine ⟨93444518538553626368608733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62296345692369084245739155 93444518538553626368608733)
            ·
              refine ⟨35041694451957609888228275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93444518538553626368608733 35041694451957609888228275)
              ·
                refine ⟨52562541677936414832342413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35041694451957609888228275 52562541677936414832342413)
                ·
                  refine ⟨19710953129226155562128405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52562541677936414832342413 19710953129226155562128405)
                  ·
                    refine ⟨923950927932476041974769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19710953129226155562128405 923950927932476041974769)
                    ·
                      rfl

theorem cell22_2699082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_2699082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699082 prefixEnd_2699082 := by exact prefixLift 2699082
  have htrace : WordTrace (prefixWord ++ tailWord_2699082) baseStart_2699082 baseEnd_2699082 := by
    simpa [prefixWord, tailWord_2699082, baseEnd_2699082] using wordTrace_append hprefix tailTrace_2699082
  have hstable : (prefixWord ++ tailWord_2699082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699082).length < 2 ^ (prefixWord ++ tailWord_2699082).sum := by decide
  have hdescent : baseEnd_2699082 < baseStart_2699082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699097 : List Nat := [1, 2, 1, 2, 2, 3, 3, 8]
def baseStart_2699097 : Nat := 118140960795 + 2699097 * 2 ^ 59
def prefixEnd_2699097 : Nat := 4983230072969 + 3 ^ 40 * 2699097 * 2
def baseEnd_2699097 : Nat := 102661784748780111427747

theorem tailTrace_2699097 : CollatzResearch.WordTrace tailWord_2699097 prefixEnd_2699097 102661784748780111427747 := by
  unfold tailWord_2699097
  simp only [CollatzResearch.WordTrace]
  refine ⟨98444155102640012913087545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65629436735093341942058363 98444155102640012913087545)
  ·
    refine ⟨73833116326980009684815659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98444155102640012913087545 73833116326980009684815659)
    ·
      refine ⟨110749674490470014527223489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73833116326980009684815659 110749674490470014527223489)
      ·
        refine ⟨83062255867852510895417617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110749674490470014527223489 83062255867852510895417617)
        ·
          refine ⟨62296691900889383171563213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83062255867852510895417617 62296691900889383171563213)
          ·
            refine ⟨23361259462833518689336205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62296691900889383171563213 23361259462833518689336205)
            ·
              refine ⟨8760472298562569508501077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23361259462833518689336205 8760472298562569508501077)
              ·
                refine ⟨102661784748780111427747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8760472298562569508501077 102661784748780111427747)
                ·
                  rfl

theorem cell22_2699097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 8].length) (baseStart_2699097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699097 prefixEnd_2699097 := by exact prefixLift 2699097
  have htrace : WordTrace (prefixWord ++ tailWord_2699097) baseStart_2699097 baseEnd_2699097 := by
    simpa [prefixWord, tailWord_2699097, baseEnd_2699097] using wordTrace_append hprefix tailTrace_2699097
  have hstable : (prefixWord ++ tailWord_2699097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699097).length < 2 ^ (prefixWord ++ tailWord_2699097).sum := by decide
  have hdescent : baseEnd_2699097 < baseStart_2699097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699182 : List Nat := [4, 1, 5, 1, 2, 1, 1, 7]
def baseStart_2699182 : Nat := 118140960795 + 2699182 * 2 ^ 59
def prefixEnd_2699182 : Nat := 4983230072969 + 3 ^ 40 * 2699182 * 2
def baseEnd_2699182 : Nat := 102665017775123234941607

theorem tailTrace_2699182 : CollatzResearch.WordTrace tailWord_2699182 prefixEnd_2699182 102665017775123234941607 := by
  unfold tailWord_2699182
  simp only [CollatzResearch.WordTrace]
  refine ⟨12305906913416509053741475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65631503538221381619954533 12305906913416509053741475)
  ·
    refine ⟨18458860370124763580612213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12305906913416509053741475 18458860370124763580612213)
    ·
      refine ⟨1730518159699196585682395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18458860370124763580612213 1730518159699196585682395)
      ·
        refine ⟨2595777239548794878523593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1730518159699196585682395 2595777239548794878523593)
        ·
          refine ⟨1946832929661596158892695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2595777239548794878523593 1946832929661596158892695)
          ·
            refine ⟨2920249394492394238339043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946832929661596158892695 2920249394492394238339043)
            ·
              refine ⟨4380374091738591357508565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2920249394492394238339043 4380374091738591357508565)
              ·
                refine ⟨102665017775123234941607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4380374091738591357508565 102665017775123234941607)
                ·
                  rfl

theorem cell22_2699182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_2699182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699182 prefixEnd_2699182 := by exact prefixLift 2699182
  have htrace : WordTrace (prefixWord ++ tailWord_2699182) baseStart_2699182 baseEnd_2699182 := by
    simpa [prefixWord, tailWord_2699182, baseEnd_2699182] using wordTrace_append hprefix tailTrace_2699182
  have hstable : (prefixWord ++ tailWord_2699182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699182).length < 2 ^ (prefixWord ++ tailWord_2699182).sum := by decide
  have hdescent : baseEnd_2699182 < baseStart_2699182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699236 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 4, 3]
def baseStart_2699236 : Nat := 118140960795 + 2699236 * 2 ^ 59
def prefixEnd_2699236 : Nat := 4983230072969 + 3 ^ 40 * 2699236 * 2
def baseEnd_2699236 : Nat := 924003645279670973624297

theorem tailTrace_2699236 : CollatzResearch.WordTrace tailWord_2699236 prefixEnd_2699236 924003645279670973624297 := by
  unfold tailWord_2699236
  simp only [CollatzResearch.WordTrace]
  refine ⟨49224612424568219826198781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65632816566090959768265041 49224612424568219826198781)
  ·
    refine ⟨18459229659213082434824543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49224612424568219826198781 18459229659213082434824543)
    ·
      refine ⟨27688844488819623652236815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18459229659213082434824543 27688844488819623652236815)
      ·
        refine ⟨41533266733229435478355223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27688844488819623652236815 41533266733229435478355223)
        ·
          refine ⟨62299900099844153217532835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41533266733229435478355223 62299900099844153217532835)
          ·
            refine ⟨93449850149766229826299253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62299900099844153217532835 93449850149766229826299253)
            ·
              refine ⟨8760923451540584046215555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93449850149766229826299253 8760923451540584046215555)
              ·
                refine ⟨13141385177310876069323333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8760923451540584046215555 13141385177310876069323333)
                ·
                  refine ⟨2464009720745789262998125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13141385177310876069323333 2464009720745789262998125)
                  ·
                    refine ⟨924003645279670973624297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2464009720745789262998125 924003645279670973624297)
                    ·
                      rfl

theorem cell22_2699236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_2699236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699236 prefixEnd_2699236 := by exact prefixLift 2699236
  have htrace : WordTrace (prefixWord ++ tailWord_2699236) baseStart_2699236 baseEnd_2699236 := by
    simpa [prefixWord, tailWord_2699236, baseEnd_2699236] using wordTrace_append hprefix tailTrace_2699236
  have hstable : (prefixWord ++ tailWord_2699236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699236).length < 2 ^ (prefixWord ++ tailWord_2699236).sum := by decide
  have hdescent : baseEnd_2699236 < baseStart_2699236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699304 : List Nat := [2, 1, 5, 3, 1, 2, 2, 1, 2, 3]
def baseStart_2699304 : Nat := 118140960795 + 2699304 * 2 ^ 59
def prefixEnd_2699304 : Nat := 4983230072969 + 3 ^ 40 * 2699304 * 2
def baseEnd_2699304 : Nat := 924026923069341462924089

theorem tailTrace_2699304 : CollatzResearch.WordTrace tailWord_2699304 prefixEnd_2699304 924026923069341462924089 := by
  unfold tailWord_2699304
  simp only [CollatzResearch.WordTrace]
  refine ⟨49225852506445043632936483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65634470008593391510581977 49225852506445043632936483)
  ·
    refine ⟨73838778759667565449404725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49225852506445043632936483 73838778759667565449404725)
    ·
      refine ⟨6922385508718834260881693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73838778759667565449404725 6922385508718834260881693)
      ·
        refine ⟨2595894565769562847830635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6922385508718834260881693 2595894565769562847830635)
        ·
          refine ⟨3893841848654344271745953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2595894565769562847830635 3893841848654344271745953)
          ·
            refine ⟨2920381386490758203809465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3893841848654344271745953 2920381386490758203809465)
            ·
              refine ⟨2190286039868068652857099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2920381386490758203809465 2190286039868068652857099)
              ·
                refine ⟨3285429059802102979285649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190286039868068652857099 3285429059802102979285649)
                ·
                  refine ⟨2464071794851577234464237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3285429059802102979285649 2464071794851577234464237)
                  ·
                    refine ⟨924026923069341462924089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2464071794851577234464237 924026923069341462924089)
                    ·
                      rfl

theorem cell22_2699304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_2699304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699304 prefixEnd_2699304 := by exact prefixLift 2699304
  have htrace : WordTrace (prefixWord ++ tailWord_2699304) baseStart_2699304 baseEnd_2699304 := by
    simpa [prefixWord, tailWord_2699304, baseEnd_2699304] using wordTrace_append hprefix tailTrace_2699304
  have hstable : (prefixWord ++ tailWord_2699304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699304).length < 2 ^ (prefixWord ++ tailWord_2699304).sum := by decide
  have hdescent : baseEnd_2699304 < baseStart_2699304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699339 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 8]
def baseStart_2699339 : Nat := 118140960795 + 2699339 * 2 ^ 59
def prefixEnd_2699339 : Nat := 4983230072969 + 3 ^ 40 * 2699339 * 2
def baseEnd_2699339 : Nat := 308012968094871012766327

theorem tailTrace_2699339 : CollatzResearch.WordTrace tailWord_2699339 prefixEnd_2699339 308012968094871012766327 := by
  unfold tailWord_2699339
  simp only [CollatzResearch.WordTrace]
  refine ⟨98452981567763288243397071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65635321045175525495598047 98452981567763288243397071)
  ·
    refine ⟨147679472351644932365095607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98452981567763288243397071 147679472351644932365095607)
    ·
      refine ⟨221519208527467398547643411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147679472351644932365095607 221519208527467398547643411)
      ·
        refine ⟨332278812791201097821465117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221519208527467398547643411 332278812791201097821465117)
        ·
          refine ⟨124604554796700411683049419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332278812791201097821465117 124604554796700411683049419)
          ·
            refine ⟨186906832195050617524574129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124604554796700411683049419 186906832195050617524574129)
            ·
              refine ⟨140180124146287963143430597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186906832195050617524574129 140180124146287963143430597)
              ·
                refine ⟨26283773277428993089393237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140180124146287963143430597 26283773277428993089393237)
                ·
                  refine ⟨308012968094871012766327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26283773277428993089393237 308012968094871012766327)
                  ·
                    rfl

theorem cell22_2699339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 8].length) (baseStart_2699339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699339 prefixEnd_2699339 := by exact prefixLift 2699339
  have htrace : WordTrace (prefixWord ++ tailWord_2699339) baseStart_2699339 baseEnd_2699339 := by
    simpa [prefixWord, tailWord_2699339, baseEnd_2699339] using wordTrace_append hprefix tailTrace_2699339
  have hstable : (prefixWord ++ tailWord_2699339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699339).length < 2 ^ (prefixWord ++ tailWord_2699339).sum := by decide
  have hdescent : baseEnd_2699339 < baseStart_2699339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699422 : List Nat := [4, 3, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_2699422 : Nat := 118140960795 + 2699422 * 2 ^ 59
def prefixEnd_2699422 : Nat := 4983230072969 + 3 ^ 40 * 2699422 * 2
def baseEnd_2699422 : Nat := 924067316880828488473727

theorem tailTrace_2699422 : CollatzResearch.WordTrace tailWord_2699422 prefixEnd_2699422 924067316880828488473727 := by
  unfold tailWord_2699422
  simp only [CollatzResearch.WordTrace]
  refine ⟨12307001103307824177333565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65637339217641728945779013 12307001103307824177333565)
  ·
    refine ⟨4615125413740434066500087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12307001103307824177333565 4615125413740434066500087)
    ·
      refine ⟨6922688120610651099750131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4615125413740434066500087 6922688120610651099750131)
      ·
        refine ⟨10384032180915976649625197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6922688120610651099750131 10384032180915976649625197)
        ·
          refine ⟨3894012067843491243609449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10384032180915976649625197 3894012067843491243609449)
          ·
            refine ⟨2920509050882618432707087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3894012067843491243609449 2920509050882618432707087)
            ·
              refine ⟨4380763576323927649060631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2920509050882618432707087 4380763576323927649060631)
              ·
                refine ⟨6571145364485891473590947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4380763576323927649060631 6571145364485891473590947)
                ·
                  refine ⟨9856718046728837210386421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6571145364485891473590947 9856718046728837210386421)
                  ·
                    refine ⟨924067316880828488473727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9856718046728837210386421 924067316880828488473727)
                    ·
                      rfl

theorem cell22_2699422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_2699422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699422 prefixEnd_2699422 := by exact prefixLift 2699422
  have htrace : WordTrace (prefixWord ++ tailWord_2699422) baseStart_2699422 baseEnd_2699422 := by
    simpa [prefixWord, tailWord_2699422, baseEnd_2699422] using wordTrace_append hprefix tailTrace_2699422
  have hstable : (prefixWord ++ tailWord_2699422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699422).length < 2 ^ (prefixWord ++ tailWord_2699422).sum := by decide
  have hdescent : baseEnd_2699422 < baseStart_2699422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699461 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 4, 5]
def baseStart_2699461 : Nat := 118140960795 + 2699461 * 2 ^ 59
def prefixEnd_2699461 : Nat := 4983230072969 + 3 ^ 40 * 2699461 * 2
def baseEnd_2699461 : Nat := 924080667377845386748607

theorem tailTrace_2699461 : CollatzResearch.WordTrace tailWord_2699461 prefixEnd_2699461 924080667377845386748607 := by
  unfold tailWord_2699461
  simp only [CollatzResearch.WordTrace]
  refine ⟨98457431273321303079338237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65638287515547535386225491 98457431273321303079338237)
  ·
    refine ⟨36921536727495488654751839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98457431273321303079338237 36921536727495488654751839)
    ·
      refine ⟨55382305091243232982127759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36921536727495488654751839 55382305091243232982127759)
      ·
        refine ⟨83073457636864849473191639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55382305091243232982127759 83073457636864849473191639)
        ·
          refine ⟨124610186455297274209787459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83073457636864849473191639 124610186455297274209787459)
          ·
            refine ⟨186915279682945911314681189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124610186455297274209787459 186915279682945911314681189)
            ·
              refine ⟨35046614940552358371502723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186915279682945911314681189 35046614940552358371502723)
              ·
                refine ⟨52569922410828537557254085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35046614940552358371502723 52569922410828537557254085)
                ·
                  refine ⟨9856860452030350791985141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52569922410828537557254085 9856860452030350791985141)
                  ·
                    refine ⟨924080667377845386748607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9856860452030350791985141 924080667377845386748607)
                    ·
                      rfl

theorem cell22_2699461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_2699461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699461 prefixEnd_2699461 := by exact prefixLift 2699461
  have htrace : WordTrace (prefixWord ++ tailWord_2699461) baseStart_2699461 baseEnd_2699461 := by
    simpa [prefixWord, tailWord_2699461, baseEnd_2699461] using wordTrace_append hprefix tailTrace_2699461
  have hstable : (prefixWord ++ tailWord_2699461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699461).length < 2 ^ (prefixWord ++ tailWord_2699461).sum := by decide
  have hdescent : baseEnd_2699461 < baseStart_2699461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699467 : List Nat := [1, 1, 1, 1, 3, 2, 7, 2, 1, 3]
def baseStart_2699467 : Nat := 118140960795 + 2699467 * 2 ^ 59
def prefixEnd_2699467 : Nat := 4983230072969 + 3 ^ 40 * 2699467 * 2
def baseEnd_2699467 : Nat := 924082721300463371098589

theorem tailTrace_2699467 : CollatzResearch.WordTrace tailWord_2699467 prefixEnd_2699467 924082721300463371098589 := by
  unfold tailWord_2699467
  simp only [CollatzResearch.WordTrace]
  refine ⟨98457650111299566104056655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65638433407533044069371103 98457650111299566104056655)
  ·
    refine ⟨147686475166949349156084983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98457650111299566104056655 147686475166949349156084983)
    ·
      refine ⟨221529712750424023734127475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147686475166949349156084983 221529712750424023734127475)
      ·
        refine ⟨332294569125636035601191213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221529712750424023734127475 332294569125636035601191213)
        ·
          refine ⟨124610463422113513350446705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332294569125636035601191213 124610463422113513350446705)
          ·
            refine ⟨93457847566585135012835029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124610463422113513350446705 93457847566585135012835029)
            ·
              refine ⟨2190418302341839101863321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 93457847566585135012835029 2190418302341839101863321)
              ·
                refine ⟨1642813726756379326397491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2190418302341839101863321 1642813726756379326397491)
                ·
                  refine ⟨2464220590134568989596237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1642813726756379326397491 2464220590134568989596237)
                  ·
                    refine ⟨924082721300463371098589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2464220590134568989596237 924082721300463371098589)
                    ·
                      rfl

theorem cell22_2699467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 1, 3].length) (baseStart_2699467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699467 prefixEnd_2699467 := by exact prefixLift 2699467
  have htrace : WordTrace (prefixWord ++ tailWord_2699467) baseStart_2699467 baseEnd_2699467 := by
    simpa [prefixWord, tailWord_2699467, baseEnd_2699467] using wordTrace_append hprefix tailTrace_2699467
  have hstable : (prefixWord ++ tailWord_2699467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699467).length < 2 ^ (prefixWord ++ tailWord_2699467).sum := by decide
  have hdescent : baseEnd_2699467 < baseStart_2699467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699480 : List Nat := [2, 1, 2, 2, 4, 1, 4, 1, 5]
def baseStart_2699480 : Nat := 118140960795 + 2699480 * 2 ^ 59
def prefixEnd_2699480 : Nat := 4983230072969 + 3 ^ 40 * 2699480 * 2
def baseEnd_2699480 : Nat := 308029057155378556841183

theorem tailTrace_2699480 : CollatzResearch.WordTrace tailWord_2699480 prefixEnd_2699480 308029057155378556841183 := by
  unfold tailWord_2699480
  simp only [CollatzResearch.WordTrace]
  refine ⟨49229062130126234662139947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65638749506834979549519929 49229062130126234662139947)
  ·
    refine ⟨73843593195189351993209921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49229062130126234662139947 73843593195189351993209921)
    ·
      refine ⟨55382694896392013994907441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73843593195189351993209921 55382694896392013994907441)
      ·
        refine ⟨41537021172294010496180581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55382694896392013994907441 41537021172294010496180581)
        ·
          refine ⟨7788191469805126968033859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41537021172294010496180581 7788191469805126968033859)
          ·
            refine ⟨11682287204707690452050789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7788191469805126968033859 11682287204707690452050789)
            ·
              refine ⟨2190428850882691959759523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11682287204707690452050789 2190428850882691959759523)
              ·
                refine ⟨3285643276324037939639285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190428850882691959759523 3285643276324037939639285)
                ·
                  refine ⟨308029057155378556841183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3285643276324037939639285 308029057155378556841183)
                  ·
                    rfl

theorem cell22_2699480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 5].length) (baseStart_2699480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699480 prefixEnd_2699480 := by exact prefixLift 2699480
  have htrace : WordTrace (prefixWord ++ tailWord_2699480) baseStart_2699480 baseEnd_2699480 := by
    simpa [prefixWord, tailWord_2699480, baseEnd_2699480] using wordTrace_append hprefix tailTrace_2699480
  have hstable : (prefixWord ++ tailWord_2699480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699480).length < 2 ^ (prefixWord ++ tailWord_2699480).sum := by decide
  have hdescent : baseEnd_2699480 < baseStart_2699480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699510 : List Nat := [5, 1, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_2699510 : Nat := 118140960795 + 2699510 * 2 ^ 59
def prefixEnd_2699510 : Nat := 4983230072969 + 3 ^ 40 * 2699510 * 2
def baseEnd_2699510 : Nat := 924097441079225592273457

theorem tailTrace_2699510 : CollatzResearch.WordTrace tailWord_2699510 prefixEnd_2699510 924097441079225592273457 := by
  unfold tailWord_2699510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6153701153133986527991999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65639478966762522965247989 6153701153133986527991999)
  ·
    refine ⟨9230551729700979791987999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6153701153133986527991999 9230551729700979791987999)
    ·
      refine ⟨13845827594551469687981999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9230551729700979791987999 13845827594551469687981999)
      ·
        refine ⟨20768741391827204531972999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13845827594551469687981999 20768741391827204531972999)
        ·
          refine ⟨31153112087740806797959499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20768741391827204531972999 31153112087740806797959499)
          ·
            refine ⟨46729668131611210196939249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31153112087740806797959499 46729668131611210196939249)
            ·
              refine ⟨35047251098708407647704437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46729668131611210196939249 35047251098708407647704437)
              ·
                refine ⟨3285679790503913216972291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35047251098708407647704437 3285679790503913216972291)
                ·
                  refine ⟨4928519685755869825458437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3285679790503913216972291 4928519685755869825458437)
                  ·
                    refine ⟨924097441079225592273457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4928519685755869825458437 924097441079225592273457)
                    ·
                      rfl

theorem cell22_2699510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_2699510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699510 prefixEnd_2699510 := by exact prefixLift 2699510
  have htrace : WordTrace (prefixWord ++ tailWord_2699510) baseStart_2699510 baseEnd_2699510 := by
    simpa [prefixWord, tailWord_2699510, baseEnd_2699510] using wordTrace_append hprefix tailTrace_2699510
  have hstable : (prefixWord ++ tailWord_2699510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699510).length < 2 ^ (prefixWord ++ tailWord_2699510).sum := by decide
  have hdescent : baseEnd_2699510 < baseStart_2699510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699649 : List Nat := [1, 2, 4, 3, 1, 3, 2, 1, 5]
def baseStart_2699649 : Nat := 118140960795 + 2699649 * 2 ^ 59
def prefixEnd_2699649 : Nat := 4983230072969 + 3 ^ 40 * 2699649 * 2
def baseEnd_2699649 : Nat := 308048341206625187682677

theorem tailTrace_2699649 : CollatzResearch.WordTrace tailWord_2699649 prefixEnd_2699649 308048341206625187682677 := by
  unfold tailWord_2699649
  simp only [CollatzResearch.WordTrace]
  refine ⟨98464288196640211187182001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65642858797760140791454667 98464288196640211187182001)
  ·
    refine ⟨73848216147480158390386501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98464288196640211187182001 73848216147480158390386501)
    ·
      refine ⟨13846540527652529698197469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73848216147480158390386501 13846540527652529698197469)
      ·
        refine ⟨5192452697869698636824051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13846540527652529698197469 5192452697869698636824051)
        ·
          refine ⟨7788679046804547955236077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5192452697869698636824051 7788679046804547955236077)
          ·
            refine ⟨2920754642551705483213529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7788679046804547955236077 2920754642551705483213529)
            ·
              refine ⟨2190565981913779112410147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2920754642551705483213529 2190565981913779112410147)
              ·
                refine ⟨3285848972870668668615221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190565981913779112410147 3285848972870668668615221)
                ·
                  refine ⟨308048341206625187682677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3285848972870668668615221 308048341206625187682677)
                  ·
                    rfl

theorem cell22_2699649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 5].length) (baseStart_2699649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699649 prefixEnd_2699649 := by exact prefixLift 2699649
  have htrace : WordTrace (prefixWord ++ tailWord_2699649) baseStart_2699649 baseEnd_2699649 := by
    simpa [prefixWord, tailWord_2699649, baseEnd_2699649] using wordTrace_append hprefix tailTrace_2699649
  have hstable : (prefixWord ++ tailWord_2699649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699649).length < 2 ^ (prefixWord ++ tailWord_2699649).sum := by decide
  have hdescent : baseEnd_2699649 < baseStart_2699649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699662 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_2699662 : Nat := 118140960795 + 2699662 * 2 ^ 59
def prefixEnd_2699662 : Nat := 4983230072969 + 3 ^ 40 * 2699662 * 2
def baseEnd_2699662 : Nat := 924149473785547862472991

theorem tailTrace_2699662 : CollatzResearch.WordTrace tailWord_2699662 prefixEnd_2699662 924149473785547862472991 := by
  unfold tailWord_2699662
  simp only [CollatzResearch.WordTrace]
  refine ⟨12308095293199139300925655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65643174897062076271603493 12308095293199139300925655)
  ·
    refine ⟨18462142939798708951388483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12308095293199139300925655 18462142939798708951388483)
    ·
      refine ⟨27693214409698063427082725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18462142939798708951388483 27693214409698063427082725)
      ·
        refine ⟨5192477701818386892578011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27693214409698063427082725 5192477701818386892578011)
        ·
          refine ⟨7788716552727580338867017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5192477701818386892578011 7788716552727580338867017)
          ·
            refine ⟨5841537414545685254150263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7788716552727580338867017 5841537414545685254150263)
            ·
              refine ⟨8762306121818527881225395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5841537414545685254150263 8762306121818527881225395)
              ·
                refine ⟨13143459182727791821838093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8762306121818527881225395 13143459182727791821838093)
                ·
                  refine ⟨4928797193522921933189285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13143459182727791821838093 4928797193522921933189285)
                  ·
                    refine ⟨924149473785547862472991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4928797193522921933189285 924149473785547862472991)
                    ·
                      rfl

theorem cell22_2699662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_2699662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699662 prefixEnd_2699662 := by exact prefixLift 2699662
  have htrace : WordTrace (prefixWord ++ tailWord_2699662) baseStart_2699662 baseEnd_2699662 := by
    simpa [prefixWord, tailWord_2699662, baseEnd_2699662] using wordTrace_append hprefix tailTrace_2699662
  have hstable : (prefixWord ++ tailWord_2699662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699662).length < 2 ^ (prefixWord ++ tailWord_2699662).sum := by decide
  have hdescent : baseEnd_2699662 < baseStart_2699662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699705 : List Nat := [1, 2, 1, 4, 3, 1, 3, 7]
def baseStart_2699705 : Nat := 118140960795 + 2699705 * 2 ^ 59
def prefixEnd_2699705 : Nat := 4983230072969 + 3 ^ 40 * 2699705 * 2
def baseEnd_2699705 : Nat := 102684910396034453738651

theorem tailTrace_2699705 : CollatzResearch.WordTrace tailWord_2699705 prefixEnd_2699705 102684910396034453738651 := by
  unfold tailWord_2699705
  simp only [CollatzResearch.WordTrace]
  refine ⟨98466330684437332751220569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65644220456291555167480379 98466330684437332751220569)
  ·
    refine ⟨73849748013327999563415427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98466330684437332751220569 73849748013327999563415427)
    ·
      refine ⟨110774622019991999345123141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73849748013327999563415427 110774622019991999345123141)
      ·
        refine ⟨20770241628748499877210589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110774622019991999345123141 20770241628748499877210589)
        ·
          refine ⟨7788840610780687453953971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20770241628748499877210589 7788840610780687453953971)
          ·
            refine ⟨11683260916171031180930957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7788840610780687453953971 11683260916171031180930957)
            ·
              refine ⟨4381222843564136692849109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11683260916171031180930957 4381222843564136692849109)
              ·
                refine ⟨102684910396034453738651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4381222843564136692849109 102684910396034453738651)
                ·
                  rfl

theorem cell22_2699705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 7].length) (baseStart_2699705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699705 prefixEnd_2699705 := by exact prefixLift 2699705
  have htrace : WordTrace (prefixWord ++ tailWord_2699705) baseStart_2699705 baseEnd_2699705 := by
    simpa [prefixWord, tailWord_2699705, baseEnd_2699705] using wordTrace_append hprefix tailTrace_2699705
  have hstable : (prefixWord ++ tailWord_2699705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699705).length < 2 ^ (prefixWord ++ tailWord_2699705).sum := by decide
  have hdescent : baseEnd_2699705 < baseStart_2699705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699724 : List Nat := [2, 2, 1, 4, 3, 2, 1, 1, 2, 4]
def baseStart_2699724 : Nat := 118140960795 + 2699724 * 2 ^ 59
def prefixEnd_2699724 : Nat := 4983230072969 + 3 ^ 40 * 2699724 * 2
def baseEnd_2699724 : Nat := 924170697652600367422801

theorem tailTrace_2699724 : CollatzResearch.WordTrace tailWord_2699724 prefixEnd_2699724 924170697652600367422801 := by
  unfold tailWord_2699724
  simp only [CollatzResearch.WordTrace]
  refine ⟨49233511835684249498081113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65644682447578999330774817 49233511835684249498081113)
  ·
    refine ⟨36925133876763187123560835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49233511835684249498081113 36925133876763187123560835)
    ·
      refine ⟨55387700815144780685341253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36925133876763187123560835 55387700815144780685341253)
      ·
        refine ⟨10385193902839646378501485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55387700815144780685341253 10385193902839646378501485)
        ·
          refine ⟨3894447713564867391938057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10385193902839646378501485 3894447713564867391938057)
          ·
            refine ⟨2920835785173650543953543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3894447713564867391938057 2920835785173650543953543)
            ·
              refine ⟨4381253677760475815930315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2920835785173650543953543 4381253677760475815930315)
              ·
                refine ⟨6571880516640713723895473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4381253677760475815930315 6571880516640713723895473)
                ·
                  refine ⟨4928910387480535292921605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6571880516640713723895473 4928910387480535292921605)
                  ·
                    refine ⟨924170697652600367422801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4928910387480535292921605 924170697652600367422801)
                    ·
                      rfl

theorem cell22_2699724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_2699724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699724 prefixEnd_2699724 := by exact prefixLift 2699724
  have htrace : WordTrace (prefixWord ++ tailWord_2699724) baseStart_2699724 baseEnd_2699724 := by
    simpa [prefixWord, tailWord_2699724, baseEnd_2699724] using wordTrace_append hprefix tailTrace_2699724
  have hstable : (prefixWord ++ tailWord_2699724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699724).length < 2 ^ (prefixWord ++ tailWord_2699724).sum := by decide
  have hdescent : baseEnd_2699724 < baseStart_2699724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699754 : List Nat := [3, 1, 3, 1, 3, 2, 2, 1, 3, 3]
def baseStart_2699754 : Nat := 118140960795 + 2699754 * 2 ^ 59
def prefixEnd_2699754 : Nat := 4983230072969 + 3 ^ 40 * 2699754 * 2
def baseEnd_2699754 : Nat := 924180967265690289172709

theorem tailTrace_2699754 : CollatzResearch.WordTrace tailWord_2699754 prefixEnd_2699754 924180967265690289172709 := by
  unfold tailWord_2699754
  simp only [CollatzResearch.WordTrace]
  refine ⟨24617029465314953529938579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65645411907506542746502877 24617029465314953529938579)
  ·
    refine ⟨36925544197972430294907869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24617029465314953529938579 36925544197972430294907869)
    ·
      refine ⟨13847079074239661360590451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36925544197972430294907869 13847079074239661360590451)
      ·
        refine ⟨20770618611359492040885677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13847079074239661360590451 20770618611359492040885677)
        ·
          refine ⟨7788981979259809515332129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20770618611359492040885677 7788981979259809515332129)
          ·
            refine ⟨5841736484444857136499097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7788981979259809515332129 5841736484444857136499097)
            ·
              refine ⟨4381302363333642852374323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5841736484444857136499097 4381302363333642852374323)
              ·
                refine ⟨6571953545000464278561485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4381302363333642852374323 6571953545000464278561485)
                ·
                  refine ⟨2464482579375174104460557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6571953545000464278561485 2464482579375174104460557)
                  ·
                    refine ⟨924180967265690289172709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2464482579375174104460557 924180967265690289172709)
                    ·
                      rfl

theorem cell22_2699754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_2699754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699754 prefixEnd_2699754 := by exact prefixLift 2699754
  have htrace : WordTrace (prefixWord ++ tailWord_2699754) baseStart_2699754 baseEnd_2699754 := by
    simpa [prefixWord, tailWord_2699754, baseEnd_2699754] using wordTrace_append hprefix tailTrace_2699754
  have hstable : (prefixWord ++ tailWord_2699754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699754).length < 2 ^ (prefixWord ++ tailWord_2699754).sum := by decide
  have hdescent : baseEnd_2699754 < baseStart_2699754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699797 : List Nat := [1, 3, 2, 1, 3, 1, 1, 5, 1, 4]
def baseStart_2699797 : Nat := 118140960795 + 2699797 * 2 ^ 59
def prefixEnd_2699797 : Nat := 4983230072969 + 3 ^ 40 * 2699797 * 2
def baseEnd_2699797 : Nat := 924195687044452510347577

theorem tailTrace_2699797 : CollatzResearch.WordTrace tailWord_2699797 prefixEnd_2699797 924195687044452510347577 := by
  unfold tailWord_2699797
  simp only [CollatzResearch.WordTrace]
  refine ⟨98469686200104032463569645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65646457466736021642379763 98469686200104032463569645)
  ·
    refine ⟨36926132325039012173838617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98469686200104032463569645 36926132325039012173838617)
    ·
      refine ⟨27694599243779259130378963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36926132325039012173838617 27694599243779259130378963)
      ·
        refine ⟨41541898865668888695568445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27694599243779259130378963 41541898865668888695568445)
        ·
          refine ⟨15578212074625833260838167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41541898865668888695568445 15578212074625833260838167)
          ·
            refine ⟨23367318111938749891257251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15578212074625833260838167 23367318111938749891257251)
            ·
              refine ⟨35050977167908124836885877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23367318111938749891257251 35050977167908124836885877)
              ·
                refine ⟨3286029109491386703458051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35050977167908124836885877 3286029109491386703458051)
                ·
                  refine ⟨4929043664237080055187077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3286029109491386703458051 4929043664237080055187077)
                  ·
                    refine ⟨924195687044452510347577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4929043664237080055187077 924195687044452510347577)
                    ·
                      rfl

theorem cell22_2699797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_2699797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699797 prefixEnd_2699797 := by exact prefixLift 2699797
  have htrace : WordTrace (prefixWord ++ tailWord_2699797) baseStart_2699797 baseEnd_2699797 := by
    simpa [prefixWord, tailWord_2699797, baseEnd_2699797] using wordTrace_append hprefix tailTrace_2699797
  have hstable : (prefixWord ++ tailWord_2699797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699797).length < 2 ^ (prefixWord ++ tailWord_2699797).sum := by decide
  have hdescent : baseEnd_2699797 < baseStart_2699797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699825 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 3, 6]
def baseStart_2699825 : Nat := 118140960795 + 2699825 * 2 ^ 59
def prefixEnd_2699825 : Nat := 4983230072969 + 3 ^ 40 * 2699825 * 2
def baseEnd_2699825 : Nat := 924205272016669770647491

theorem tailTrace_2699825 : CollatzResearch.WordTrace tailWord_2699825 prefixEnd_2699825 924205272016669770647491 := by
  unfold tailWord_2699825
  simp only [CollatzResearch.WordTrace]
  refine ⟨98470707444002593245588929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65647138296001728830392619 98470707444002593245588929)
  ·
    refine ⟨73853030583001944934191697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98470707444002593245588929 73853030583001944934191697)
    ·
      refine ⟨55389772937251458700643773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73853030583001944934191697 55389772937251458700643773)
      ·
        refine ⟨20771164851469297012741415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55389772937251458700643773 20771164851469297012741415)
        ·
          refine ⟨31156747277203945519112123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20771164851469297012741415 31156747277203945519112123)
          ·
            refine ⟨46735120915805918278668185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31156747277203945519112123 46735120915805918278668185)
            ·
              refine ⟨35051340686854438709001139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46735120915805918278668185 35051340686854438709001139)
              ·
                refine ⟨52577011030281658063501709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35051340686854438709001139 52577011030281658063501709)
                ·
                  refine ⟨19716379136355621773813141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52577011030281658063501709 19716379136355621773813141)
                  ·
                    refine ⟨924205272016669770647491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19716379136355621773813141 924205272016669770647491)
                    ·
                      rfl

theorem cell22_2699825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_2699825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699825 prefixEnd_2699825 := by exact prefixLift 2699825
  have htrace : WordTrace (prefixWord ++ tailWord_2699825) baseStart_2699825 baseEnd_2699825 := by
    simpa [prefixWord, tailWord_2699825, baseEnd_2699825] using wordTrace_append hprefix tailTrace_2699825
  have hstable : (prefixWord ++ tailWord_2699825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699825).length < 2 ^ (prefixWord ++ tailWord_2699825).sum := by decide
  have hdescent : baseEnd_2699825 < baseStart_2699825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699840 : List Nat := [2, 1, 1, 2, 2, 2, 4, 8]
def baseStart_2699840 : Nat := 118140960795 + 2699840 * 2 ^ 59
def prefixEnd_2699840 : Nat := 4983230072969 + 3 ^ 40 * 2699840 * 2
def baseEnd_2699840 : Nat := 102690045202579414613605

theorem tailTrace_2699840 : CollatzResearch.WordTrace tailWord_2699840 prefixEnd_2699840 102690045202579414613605 := by
  unfold tailWord_2699840
  simp only [CollatzResearch.WordTrace]
  refine ⟨49235627269474125403692487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65647503025965500538256649 49235627269474125403692487)
  ·
    refine ⟨73853440904211188105538731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49235627269474125403692487 73853440904211188105538731)
    ·
      refine ⟨110780161356316782158308097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73853440904211188105538731 110780161356316782158308097)
      ·
        refine ⟨83085121017237586618731073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110780161356316782158308097 83085121017237586618731073)
        ·
          refine ⟨62313840762928189964048305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83085121017237586618731073 62313840762928189964048305)
          ·
            refine ⟨46735380572196142473036229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62313840762928189964048305 46735380572196142473036229)
            ·
              refine ⟨8762883857286776713694293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46735380572196142473036229 8762883857286776713694293)
              ·
                refine ⟨102690045202579414613605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8762883857286776713694293 102690045202579414613605)
                ·
                  rfl

theorem cell22_2699840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 8].length) (baseStart_2699840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699840 prefixEnd_2699840 := by exact prefixLift 2699840
  have htrace : WordTrace (prefixWord ++ tailWord_2699840) baseStart_2699840 baseEnd_2699840 := by
    simpa [prefixWord, tailWord_2699840, baseEnd_2699840] using wordTrace_append hprefix tailTrace_2699840
  have hstable : (prefixWord ++ tailWord_2699840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699840).length < 2 ^ (prefixWord ++ tailWord_2699840).sum := by decide
  have hdescent : baseEnd_2699840 < baseStart_2699840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699893 : List Nat := [1, 3, 4, 2, 3, 1, 1, 1, 2, 4]
def baseStart_2699893 : Nat := 118140960795 + 2699893 * 2 ^ 59
def prefixEnd_2699893 : Nat := 4983230072969 + 3 ^ 40 * 2699893 * 2
def baseEnd_2699893 : Nat := 924228549806340259947283

theorem tailTrace_2699893 : CollatzResearch.WordTrace tailWord_2699893 prefixEnd_2699893 924228549806340259947283 := by
  unfold tailWord_2699893
  simp only [CollatzResearch.WordTrace]
  refine ⟨98473187607756240859064333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65648791738504160572709555 98473187607756240859064333)
  ·
    refine ⟨36927445352908590322149125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98473187607756240859064333 36927445352908590322149125)
    ·
      refine ⟨6923896003670360685402961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36927445352908590322149125 6923896003670360685402961)
      ·
        refine ⟨5192922002752770514052221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6923896003670360685402961 5192922002752770514052221)
        ·
          refine ⟨1947345751032288942769583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5192922002752770514052221 1947345751032288942769583)
          ·
            refine ⟨2921018626548433414154375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1947345751032288942769583 2921018626548433414154375)
            ·
              refine ⟨4381527939822650121231563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2921018626548433414154375 4381527939822650121231563)
              ·
                refine ⟨6572291909733975181847345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4381527939822650121231563 6572291909733975181847345)
                ·
                  refine ⟨4929218932300481386385509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6572291909733975181847345 4929218932300481386385509)
                  ·
                    refine ⟨924228549806340259947283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4929218932300481386385509 924228549806340259947283)
                    ·
                      rfl

theorem cell22_2699893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_2699893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699893 prefixEnd_2699893 := by exact prefixLift 2699893
  have htrace : WordTrace (prefixWord ++ tailWord_2699893) baseStart_2699893 baseEnd_2699893 := by
    simpa [prefixWord, tailWord_2699893, baseEnd_2699893] using wordTrace_append hprefix tailTrace_2699893
  have hstable : (prefixWord ++ tailWord_2699893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699893).length < 2 ^ (prefixWord ++ tailWord_2699893).sum := by decide
  have hdescent : baseEnd_2699893 < baseStart_2699893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699934 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_2699934 : Nat := 118140960795 + 2699934 * 2 ^ 59
def prefixEnd_2699934 : Nat := 4983230072969 + 3 ^ 40 * 2699934 * 2
def baseEnd_2699934 : Nat := 924242584944229819672157

theorem tailTrace_2699934 : CollatzResearch.WordTrace tailWord_2699934 prefixEnd_2699934 924242584944229819672157 := by
  unfold tailWord_2699934
  simp only [CollatzResearch.WordTrace]
  refine ⟨12309335375075963107663357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65649788667071803240871237 12309335375075963107663357)
  ·
    refine ⟨4616000765653486165373759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12309335375075963107663357 4616000765653486165373759)
    ·
      refine ⟨6924001148480229248060639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4616000765653486165373759 6924001148480229248060639)
      ·
        refine ⟨10386001722720343872090959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6924001148480229248060639 10386001722720343872090959)
        ·
          refine ⟨15579002584080515808136439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10386001722720343872090959 15579002584080515808136439)
          ·
            refine ⟨23368503876120773712204659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15579002584080515808136439 23368503876120773712204659)
            ·
              refine ⟨35052755814181160568306989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23368503876120773712204659 35052755814181160568306989)
              ·
                refine ⟨13144783430317935213115121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35052755814181160568306989 13144783430317935213115121)
                ·
                  refine ⟨9858587572738451409836341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13144783430317935213115121 9858587572738451409836341)
                  ·
                    refine ⟨924242584944229819672157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9858587572738451409836341 924242584944229819672157)
                    ·
                      rfl

theorem cell22_2699934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_2699934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699934 prefixEnd_2699934 := by exact prefixLift 2699934
  have htrace : WordTrace (prefixWord ++ tailWord_2699934) baseStart_2699934 baseEnd_2699934 := by
    simpa [prefixWord, tailWord_2699934, baseEnd_2699934] using wordTrace_append hprefix tailTrace_2699934
  have hstable : (prefixWord ++ tailWord_2699934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699934).length < 2 ^ (prefixWord ++ tailWord_2699934).sum := by decide
  have hdescent : baseEnd_2699934 < baseStart_2699934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699936 : List Nat := [2, 1, 1, 4, 4, 1, 3, 1, 5]
def baseStart_2699936 : Nat := 118140960795 + 2699936 * 2 ^ 59
def prefixEnd_2699936 : Nat := 4983230072969 + 3 ^ 40 * 2699936 * 2
def baseEnd_2699936 : Nat := 308081089861700827040717

theorem tailTrace_2699936 : CollatzResearch.WordTrace tailWord_2699936 prefixEnd_2699936 308081089861700827040717 := by
  unfold tailWord_2699936
  simp only [CollatzResearch.WordTrace]
  refine ⟨49237377973300229601439831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65649837297733639468586441 49237377973300229601439831)
  ·
    refine ⟨73856066959950344402159747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49237377973300229601439831 73856066959950344402159747)
    ·
      refine ⟨110784100439925516603239621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73856066959950344402159747 110784100439925516603239621)
      ·
        refine ⟨20772018832486034363107429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110784100439925516603239621 20772018832486034363107429)
        ·
          refine ⟨3894753531091131443082643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20772018832486034363107429 3894753531091131443082643)
          ·
            refine ⟨5842130296636697164623965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3894753531091131443082643 5842130296636697164623965)
            ·
              refine ⟨2190798861238761436733987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5842130296636697164623965 2190798861238761436733987)
              ·
                refine ⟨3286198291858142155100981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190798861238761436733987 3286198291858142155100981)
                ·
                  refine ⟨308081089861700827040717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3286198291858142155100981 308081089861700827040717)
                  ·
                    rfl

theorem cell22_2699936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 5].length) (baseStart_2699936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699936 prefixEnd_2699936 := by exact prefixLift 2699936
  have htrace : WordTrace (prefixWord ++ tailWord_2699936) baseStart_2699936 baseEnd_2699936 := by
    simpa [prefixWord, tailWord_2699936, baseEnd_2699936] using wordTrace_append hprefix tailTrace_2699936
  have hstable : (prefixWord ++ tailWord_2699936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699936).length < 2 ^ (prefixWord ++ tailWord_2699936).sum := by decide
  have hdescent : baseEnd_2699936 < baseStart_2699936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699962 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 3, 5]
def baseStart_2699962 : Nat := 118140960795 + 2699962 * 2 ^ 59
def prefixEnd_2699962 : Nat := 4983230072969 + 3 ^ 40 * 2699962 * 2
def baseEnd_2699962 : Nat := 924252169916447079972071

theorem tailTrace_2699962 : CollatzResearch.WordTrace tailWord_2699962 prefixEnd_2699962 924252169916447079972071 := by
  unfold tailWord_2699962
  simp only [CollatzResearch.WordTrace]
  refine ⟨24618926061126566410831535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65650469496337510428884093 24618926061126566410831535)
  ·
    refine ⟨36928389091689849616247303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24618926061126566410831535 36928389091689849616247303)
    ·
      refine ⟨55392583637534774424370955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36928389091689849616247303 55392583637534774424370955)
      ·
        refine ⟨83088875456302161636556433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55392583637534774424370955 83088875456302161636556433)
        ·
          refine ⟨62316656592226621227417325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83088875456302161636556433 62316656592226621227417325)
          ·
            refine ⟨23368746222084982960281497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62316656592226621227417325 23368746222084982960281497)
            ·
              refine ⟨17526559666563737220211123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23368746222084982960281497 17526559666563737220211123)
              ·
                refine ⟨26289839499845605830316685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17526559666563737220211123 26289839499845605830316685)
                ·
                  refine ⟨9858689812442102186368757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26289839499845605830316685 9858689812442102186368757)
                  ·
                    refine ⟨924252169916447079972071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9858689812442102186368757 924252169916447079972071)
                    ·
                      rfl

theorem cell22_2699962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_2699962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699962 prefixEnd_2699962 := by exact prefixLift 2699962
  have htrace : WordTrace (prefixWord ++ tailWord_2699962) baseStart_2699962 baseEnd_2699962 := by
    simpa [prefixWord, tailWord_2699962, baseEnd_2699962] using wordTrace_append hprefix tailTrace_2699962
  have hstable : (prefixWord ++ tailWord_2699962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699962).length < 2 ^ (prefixWord ++ tailWord_2699962).sum := by decide
  have hdescent : baseEnd_2699962 < baseStart_2699962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699974 : List Nat := [6, 1, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_2699974 : Nat := 118140960795 + 2699974 * 2 ^ 59
def prefixEnd_2699974 : Nat := 4983230072969 + 3 ^ 40 * 2699974 * 2
def baseEnd_2699974 : Nat := 924256277761683048672035

theorem tailTrace_2699974 : CollatzResearch.WordTrace tailWord_2699974 prefixEnd_2699974 924256277761683048672035 := by
  unfold tailWord_2699974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3077379435014462240398843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65650761280308527795175317 3077379435014462240398843)
  ·
    refine ⟨4616069152521693360598265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3077379435014462240398843 4616069152521693360598265)
    ·
      refine ⟨3462051864391270020448699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4616069152521693360598265 3462051864391270020448699)
      ·
        refine ⟨5193077796586905030673049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3462051864391270020448699 5193077796586905030673049)
        ·
          refine ⟨3894808347440178773004787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5193077796586905030673049 3894808347440178773004787)
          ·
            refine ⟨5842212521160268159507181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3894808347440178773004787 5842212521160268159507181)
            ·
              refine ⟨2190829695435100559815193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5842212521160268159507181 2190829695435100559815193)
              ·
                refine ⟨1643122271576325419861395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2190829695435100559815193 1643122271576325419861395)
                ·
                  refine ⟨2464683407364488129792093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643122271576325419861395 2464683407364488129792093)
                  ·
                    refine ⟨924256277761683048672035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2464683407364488129792093 924256277761683048672035)
                    ·
                      rfl

theorem cell22_2699974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_2699974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699974 prefixEnd_2699974 := by exact prefixLift 2699974
  have htrace : WordTrace (prefixWord ++ tailWord_2699974) baseStart_2699974 baseEnd_2699974 := by
    simpa [prefixWord, tailWord_2699974, baseEnd_2699974] using wordTrace_append hprefix tailTrace_2699974
  have hstable : (prefixWord ++ tailWord_2699974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699974).length < 2 ^ (prefixWord ++ tailWord_2699974).sum := by decide
  have hdescent : baseEnd_2699974 < baseStart_2699974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2699992 : List Nat := [2, 1, 2, 2, 3, 2, 1, 9]
def baseStart_2699992 : Nat := 118140960795 + 2699992 * 2 ^ 59
def prefixEnd_2699992 : Nat := 4983230072969 + 3 ^ 40 * 2699992 * 2
def baseEnd_2699992 : Nat := 102695826614393000191331

theorem tailTrace_2699992 : CollatzResearch.WordTrace tailWord_2699992 prefixEnd_2699992 102695826614393000191331 := by
  unfold tailWord_2699992
  simp only [CollatzResearch.WordTrace]
  refine ⟨49238399217198790383459115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65651198956265053844612153 49238399217198790383459115)
  ·
    refine ⟨73857598825798185575188673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49238399217198790383459115 73857598825798185575188673)
    ·
      refine ⟨55393199119348639181391505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73857598825798185575188673 55393199119348639181391505)
      ·
        refine ⟨41544899339511479386043629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55393199119348639181391505 41544899339511479386043629)
        ·
          refine ⟨15579337252316804769766361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41544899339511479386043629 15579337252316804769766361)
          ·
            refine ⟨11684502939237603577324771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15579337252316804769766361 11684502939237603577324771)
            ·
              refine ⟨17526754408856405365987157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11684502939237603577324771 17526754408856405365987157)
              ·
                refine ⟨102695826614393000191331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17526754408856405365987157 102695826614393000191331)
                ·
                  rfl

theorem cell22_2699992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 9].length) (baseStart_2699992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2699992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2699992 prefixEnd_2699992 := by exact prefixLift 2699992
  have htrace : WordTrace (prefixWord ++ tailWord_2699992) baseStart_2699992 baseEnd_2699992 := by
    simpa [prefixWord, tailWord_2699992, baseEnd_2699992] using wordTrace_append hprefix tailTrace_2699992
  have hstable : (prefixWord ++ tailWord_2699992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2699992).length < 2 ^ (prefixWord ++ tailWord_2699992).sum := by decide
  have hdescent : baseEnd_2699992 < baseStart_2699992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2699992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700037 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 7]
def baseStart_2700037 : Nat := 118140960795 + 2700037 * 2 ^ 59
def prefixEnd_2700037 : Nat := 4983230072969 + 3 ^ 40 * 2700037 * 2
def baseEnd_2700037 : Nat := 308092614649723961448947

theorem tailTrace_2700037 : CollatzResearch.WordTrace tailWord_2700037 prefixEnd_2700037 308092614649723961448947 := by
  unfold tailWord_2700037
  simp only [CollatzResearch.WordTrace]
  refine ⟨98478439719234553452306365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65652293146156368968204243 98478439719234553452306365)
  ·
    refine ⟨36929414894712957544614887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98478439719234553452306365 36929414894712957544614887)
    ·
      refine ⟨55394122342069436316922331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36929414894712957544614887 55394122342069436316922331)
      ·
        refine ⟨83091183513104154475383497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55394122342069436316922331 83091183513104154475383497)
        ·
          refine ⟨62318387634828115856537623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83091183513104154475383497 62318387634828115856537623)
          ·
            refine ⟨93477581452242173784806435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62318387634828115856537623 93477581452242173784806435)
            ·
              refine ⟨140216372178363260677209653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93477581452242173784806435 140216372178363260677209653)
              ·
                refine ⟨13145284891721555688488405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140216372178363260677209653 13145284891721555688488405)
                ·
                  refine ⟨308092614649723961448947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13145284891721555688488405 308092614649723961448947)
                  ·
                    rfl

theorem cell22_2700037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_2700037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700037 prefixEnd_2700037 := by exact prefixLift 2700037
  have htrace : WordTrace (prefixWord ++ tailWord_2700037) baseStart_2700037 baseEnd_2700037 := by
    simpa [prefixWord, tailWord_2700037, baseEnd_2700037] using wordTrace_append hprefix tailTrace_2700037
  have hstable : (prefixWord ++ tailWord_2700037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700037).length < 2 ^ (prefixWord ++ tailWord_2700037).sum := by decide
  have hdescent : baseEnd_2700037 < baseStart_2700037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700039 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 2, 6]
def baseStart_2700039 : Nat := 118140960795 + 2700039 * 2 ^ 59
def prefixEnd_2700039 : Nat := 4983230072969 + 3 ^ 40 * 2700039 * 2
def baseEnd_2700039 : Nat := 924278528590044545796835

theorem tailTrace_2700039 : CollatzResearch.WordTrace tailWord_2700039 prefixEnd_2700039 924278528590044545796835 := by
  unfold tailWord_2700039
  simp only [CollatzResearch.WordTrace]
  refine ⟨98478512665227307793879171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65652341776818205195919447 98478512665227307793879171)
  ·
    refine ⟨147717768997840961690818757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98478512665227307793879171 147717768997840961690818757)
    ·
      refine ⟨27697081687095180317028517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147717768997840961690818757 27697081687095180317028517)
      ·
        refine ⟨5193202816330346309442847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27697081687095180317028517 5193202816330346309442847)
        ·
          refine ⟨7789804224495519464164271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5193202816330346309442847 7789804224495519464164271)
          ·
            refine ⟨11684706336743279196246407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7789804224495519464164271 11684706336743279196246407)
            ·
              refine ⟨17527059505114918794369611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11684706336743279196246407 17527059505114918794369611)
              ·
                refine ⟨26290589257672378191554417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17527059505114918794369611 26290589257672378191554417)
                ·
                  refine ⟨19717941943254283643665813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26290589257672378191554417 19717941943254283643665813)
                  ·
                    refine ⟨924278528590044545796835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19717941943254283643665813 924278528590044545796835)
                    ·
                      rfl

theorem cell22_2700039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_2700039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700039 prefixEnd_2700039 := by exact prefixLift 2700039
  have htrace : WordTrace (prefixWord ++ tailWord_2700039) baseStart_2700039 baseEnd_2700039 := by
    simpa [prefixWord, tailWord_2700039, baseEnd_2700039] using wordTrace_append hprefix tailTrace_2700039
  have hstable : (prefixWord ++ tailWord_2700039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700039).length < 2 ^ (prefixWord ++ tailWord_2700039).sum := by decide
  have hdescent : baseEnd_2700039 < baseStart_2700039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700099 : List Nat := [1, 1, 1, 3, 1, 4, 4, 1, 6]
def baseStart_2700099 : Nat := 118140960795 + 2700099 * 2 ^ 59
def prefixEnd_2700099 : Nat := 4983230072969 + 3 ^ 40 * 2700099 * 2
def baseEnd_2700099 : Nat := 308099689272074796432217

theorem tailTrace_2700099 : CollatzResearch.WordTrace tailWord_2700099 prefixEnd_2700099 308099689272074796432217 := by
  unfold tailWord_2700099
  simp only [CollatzResearch.WordTrace]
  refine ⟨98480701045009938041063351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65653800696673292027375567 98480701045009938041063351)
  ·
    refine ⟨147721051567514907061595027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98480701045009938041063351 147721051567514907061595027)
    ·
      refine ⟨221581577351272360592392541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147721051567514907061595027 221581577351272360592392541)
      ·
        refine ⟨83093091506727135222147203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221581577351272360592392541 83093091506727135222147203)
        ·
          refine ⟨124639637260090702833220805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83093091506727135222147203 124639637260090702833220805)
          ·
            refine ⟨23369931986267006781228901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124639637260090702833220805 23369931986267006781228901)
            ·
              refine ⟨4381862247425063771480419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23369931986267006781228901 4381862247425063771480419)
              ·
                refine ⟨6572793371137595657220629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4381862247425063771480419 6572793371137595657220629)
                ·
                  refine ⟨308099689272074796432217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6572793371137595657220629 308099689272074796432217)
                  ·
                    rfl

theorem cell22_2700099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 6].length) (baseStart_2700099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700099 prefixEnd_2700099 := by exact prefixLift 2700099
  have htrace : WordTrace (prefixWord ++ tailWord_2700099) baseStart_2700099 baseEnd_2700099 := by
    simpa [prefixWord, tailWord_2700099, baseEnd_2700099] using wordTrace_append hprefix tailTrace_2700099
  have hstable : (prefixWord ++ tailWord_2700099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700099).length < 2 ^ (prefixWord ++ tailWord_2700099).sum := by decide
  have hdescent : baseEnd_2700099 < baseStart_2700099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700131 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 4, 3]
def baseStart_2700131 : Nat := 118140960795 + 2700131 * 2 ^ 59
def prefixEnd_2700131 : Nat := 4983230072969 + 3 ^ 40 * 2700131 * 2
def baseEnd_2700131 : Nat := 924310022070186972496553

theorem tailTrace_2700131 : CollatzResearch.WordTrace tailWord_2700131 prefixEnd_2700131 924310022070186972496553 := by
  unfold tailWord_2700131
  simp only [CollatzResearch.WordTrace]
  refine ⟨98481868180894007506228247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65654578787262671670818831 98481868180894007506228247)
  ·
    refine ⟨147722802271341011259342371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98481868180894007506228247 147722802271341011259342371)
    ·
      refine ⟨221584203407011516889013557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147722802271341011259342371 221584203407011516889013557)
      ·
        refine ⟨20773519069407329708345021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 221584203407011516889013557 20773519069407329708345021)
        ·
          refine ⟨7790069651027748640629383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20773519069407329708345021 7790069651027748640629383)
          ·
            refine ⟨11685104476541622960944075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7790069651027748640629383 11685104476541622960944075)
            ·
              refine ⟨17527656714812434441416113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11685104476541622960944075 17527656714812434441416113)
              ·
                refine ⟨13145742536109325831062085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17527656714812434441416113 13145742536109325831062085)
                ·
                  refine ⟨2464826725520498593324141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13145742536109325831062085 2464826725520498593324141)
                  ·
                    refine ⟨924310022070186972496553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2464826725520498593324141 924310022070186972496553)
                    ·
                      rfl

theorem cell22_2700131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 3].length) (baseStart_2700131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700131 prefixEnd_2700131 := by exact prefixLift 2700131
  have htrace : WordTrace (prefixWord ++ tailWord_2700131) baseStart_2700131 baseEnd_2700131 := by
    simpa [prefixWord, tailWord_2700131, baseEnd_2700131] using wordTrace_append hprefix tailTrace_2700131
  have hstable : (prefixWord ++ tailWord_2700131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700131).length < 2 ^ (prefixWord ++ tailWord_2700131).sum := by decide
  have hdescent : baseEnd_2700131 < baseStart_2700131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700165 : List Nat := [1, 3, 1, 1, 3, 5, 2, 1, 2, 3]
def baseStart_2700165 : Nat := 118140960795 + 2700165 * 2 ^ 59
def prefixEnd_2700165 : Nat := 4983230072969 + 3 ^ 40 * 2700165 * 2
def baseEnd_2700165 : Nat := 924321660965022217146449

theorem tailTrace_2700165 : CollatzResearch.WordTrace tailWord_2700165 prefixEnd_2700165 924321660965022217146449 := by
  unfold tailWord_2700165
  simp only [CollatzResearch.WordTrace]
  refine ⟨98483108262770831312965949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65655405508513887541977299 98483108262770831312965949)
  ·
    refine ⟨36931165598539061742362231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98483108262770831312965949 36931165598539061742362231)
    ·
      refine ⟨55396748397808592613543347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36931165598539061742362231 55396748397808592613543347)
      ·
        refine ⟨83095122596712888920315021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55396748397808592613543347 83095122596712888920315021)
        ·
          refine ⟨31160670973767333345118133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83095122596712888920315021 31160670973767333345118133)
          ·
            refine ⟨2921312903790687501104825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31160670973767333345118133 2921312903790687501104825)
            ·
              refine ⟨2190984677843015625828619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2921312903790687501104825 2190984677843015625828619)
              ·
                refine ⟨3286477016764523438742929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190984677843015625828619 3286477016764523438742929)
                ·
                  refine ⟨2464857762573392579057197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3286477016764523438742929 2464857762573392579057197)
                  ·
                    refine ⟨924321660965022217146449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2464857762573392579057197 924321660965022217146449)
                    ·
                      rfl

theorem cell22_2700165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 2, 3].length) (baseStart_2700165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700165 prefixEnd_2700165 := by exact prefixLift 2700165
  have htrace : WordTrace (prefixWord ++ tailWord_2700165) baseStart_2700165 baseEnd_2700165 := by
    simpa [prefixWord, tailWord_2700165, baseEnd_2700165] using wordTrace_append hprefix tailTrace_2700165
  have hstable : (prefixWord ++ tailWord_2700165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700165).length < 2 ^ (prefixWord ++ tailWord_2700165).sum := by decide
  have hdescent : baseEnd_2700165 < baseStart_2700165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700204 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 4, 5]
def baseStart_2700204 : Nat := 118140960795 + 2700204 * 2 ^ 59
def prefixEnd_2700204 : Nat := 4983230072969 + 3 ^ 40 * 2700204 * 2
def baseEnd_2700204 : Nat := 924335011462039115421329

theorem tailTrace_2700204 : CollatzResearch.WordTrace tailWord_2700204 prefixEnd_2700204 924335011462039115421329 := by
  unfold tailWord_2700204
  simp only [CollatzResearch.WordTrace]
  refine ⟨49242265354814770486817833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65656353806419693982423777 49242265354814770486817833)
  ·
    refine ⟨36931699016111077865113375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49242265354814770486817833 36931699016111077865113375)
    ·
      refine ⟨55397548524166616797670063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36931699016111077865113375 55397548524166616797670063)
      ·
        refine ⟨83096322786249925196505095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55397548524166616797670063 83096322786249925196505095)
        ·
          refine ⟨124644484179374887794757643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83096322786249925196505095 124644484179374887794757643)
          ·
            refine ⟨186966726269062331692136465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124644484179374887794757643 186966726269062331692136465)
            ·
              refine ⟨140225044701796748769102349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186966726269062331692136465 140225044701796748769102349)
              ·
                refine ⟨52584391763173780788413381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140225044701796748769102349 52584391763173780788413381)
                ·
                  refine ⟨9859573455595083897827509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52584391763173780788413381 9859573455595083897827509)
                  ·
                    refine ⟨924335011462039115421329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9859573455595083897827509 924335011462039115421329)
                    ·
                      rfl

theorem cell22_2700204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_2700204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700204 prefixEnd_2700204 := by exact prefixLift 2700204
  have htrace : WordTrace (prefixWord ++ tailWord_2700204) baseStart_2700204 baseEnd_2700204 := by
    simpa [prefixWord, tailWord_2700204, baseEnd_2700204] using wordTrace_append hprefix tailTrace_2700204
  have hstable : (prefixWord ++ tailWord_2700204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700204).length < 2 ^ (prefixWord ++ tailWord_2700204).sum := by decide
  have hdescent : baseEnd_2700204 < baseStart_2700204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700236 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 3, 4]
def baseStart_2700236 : Nat := 118140960795 + 2700236 * 2 ^ 59
def prefixEnd_2700236 : Nat := 4983230072969 + 3 ^ 40 * 2700236 * 2
def baseEnd_2700236 : Nat := 924345965716001698621231

theorem tailTrace_2700236 : CollatzResearch.WordTrace tailWord_2700236 prefixEnd_2700236 924345965716001698621231 := by
  unfold tailWord_2700236
  simp only [CollatzResearch.WordTrace]
  refine ⟨49242848922756805219400281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65657131897009073625867041 49242848922756805219400281)
  ·
    refine ⟨36932136692067603914550211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49242848922756805219400281 36932136692067603914550211)
    ·
      refine ⟨55398205038101405871825317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36932136692067603914550211 55398205038101405871825317)
      ·
        refine ⟨10387163444644013600967247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55398205038101405871825317 10387163444644013600967247)
        ·
          refine ⟨15580745166966020401450871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10387163444644013600967247 15580745166966020401450871)
          ·
            refine ⟨23371117750449030602176307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15580745166966020401450871 23371117750449030602176307)
            ·
              refine ⟨35056676625673545903264461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23371117750449030602176307 35056676625673545903264461)
              ·
                refine ⟨13146253734627579713724173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35056676625673545903264461 13146253734627579713724173)
                ·
                  refine ⟨4929845150485342392646565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13146253734627579713724173 4929845150485342392646565)
                  ·
                    refine ⟨924345965716001698621231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4929845150485342392646565 924345965716001698621231)
                    ·
                      rfl

theorem cell22_2700236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_2700236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700236 prefixEnd_2700236 := by exact prefixLift 2700236
  have htrace : WordTrace (prefixWord ++ tailWord_2700236) baseStart_2700236 baseEnd_2700236 := by
    simpa [prefixWord, tailWord_2700236, baseEnd_2700236] using wordTrace_append hprefix tailTrace_2700236
  have hstable : (prefixWord ++ tailWord_2700236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700236).length < 2 ^ (prefixWord ++ tailWord_2700236).sum := by decide
  have hdescent : baseEnd_2700236 < baseStart_2700236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700296 : List Nat := [2, 1, 3, 2, 1, 4, 1, 8]
def baseStart_2700296 : Nat := 118140960795 + 2700296 * 2 ^ 59
def prefixEnd_2700296 : Nat := 4983230072969 + 3 ^ 40 * 2700296 * 2
def baseEnd_2700296 : Nat := 102707389438020171346783

theorem tailTrace_2700296 : CollatzResearch.WordTrace tailWord_2700296 prefixEnd_2700296 102707389438020171346783 := by
  unfold tailWord_2700296
  simp only [CollatzResearch.WordTrace]
  refine ⟨49243943112648120342992371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65658590816864160457323161 49243943112648120342992371)
  ·
    refine ⟨73865914668972180514488557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49243943112648120342992371 73865914668972180514488557)
    ·
      refine ⟨27699718000864567692933209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73865914668972180514488557 27699718000864567692933209)
      ·
        refine ⟨20774788500648425769699907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27699718000864567692933209 20774788500648425769699907)
        ·
          refine ⟨31162182750972638654549861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20774788500648425769699907 31162182750972638654549861)
          ·
            refine ⟨5842909265807369747728099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31162182750972638654549861 5842909265807369747728099)
            ·
              refine ⟨8764363898711054621592149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5842909265807369747728099 8764363898711054621592149)
              ·
                refine ⟨102707389438020171346783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8764363898711054621592149 102707389438020171346783)
                ·
                  rfl

theorem cell22_2700296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 8].length) (baseStart_2700296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700296 prefixEnd_2700296 := by exact prefixLift 2700296
  have htrace : WordTrace (prefixWord ++ tailWord_2700296) baseStart_2700296 baseEnd_2700296 := by
    simpa [prefixWord, tailWord_2700296, baseEnd_2700296] using wordTrace_append hprefix tailTrace_2700296
  have hstable : (prefixWord ++ tailWord_2700296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700296).length < 2 ^ (prefixWord ++ tailWord_2700296).sum := by decide
  have hdescent : baseEnd_2700296 < baseStart_2700296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700371 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 5, 4]
def baseStart_2700371 : Nat := 118140960795 + 2700371 * 2 ^ 59
def prefixEnd_2700371 : Nat := 4983230072969 + 3 ^ 40 * 2700371 * 2
def baseEnd_2700371 : Nat := 924392178974906346495817

theorem tailTrace_2700371 : CollatzResearch.WordTrace tailWord_2700371 prefixEnd_2700371 924392178974906346495817 := by
  unfold tailWord_2700371
  simp only [CollatzResearch.WordTrace]
  refine ⟨98490621700024528494964967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65660414466683018996643311 98490621700024528494964967)
  ·
    refine ⟨147735932550036792742447451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98490621700024528494964967 147735932550036792742447451)
    ·
      refine ⟨221603898825055189113671177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147735932550036792742447451 221603898825055189113671177)
      ·
        refine ⟨166202924118791391835253383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221603898825055189113671177 166202924118791391835253383)
        ·
          refine ⟨249304386178187087752880075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166202924118791391835253383 249304386178187087752880075)
          ·
            refine ⟨373956579267280631629320113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249304386178187087752880075 373956579267280631629320113)
            ·
              refine ⟨280467434450460473721990085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373956579267280631629320113 280467434450460473721990085)
              ·
                refine ⟨52587643959461338822873141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 280467434450460473721990085 52587643959461338822873141)
                ·
                  refine ⟨4930091621199500514644357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52587643959461338822873141 4930091621199500514644357)
                  ·
                    refine ⟨924392178974906346495817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4930091621199500514644357 924392178974906346495817)
                    ·
                      rfl

theorem cell22_2700371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 4].length) (baseStart_2700371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700371 prefixEnd_2700371 := by exact prefixLift 2700371
  have htrace : WordTrace (prefixWord ++ tailWord_2700371) baseStart_2700371 baseEnd_2700371 := by
    simpa [prefixWord, tailWord_2700371, baseEnd_2700371] using wordTrace_append hprefix tailTrace_2700371
  have hstable : (prefixWord ++ tailWord_2700371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700371).length < 2 ^ (prefixWord ++ tailWord_2700371).sum := by decide
  have hdescent : baseEnd_2700371 < baseStart_2700371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700420 : List Nat := [2, 3, 2, 1, 2, 2, 1, 5, 4]
def baseStart_2700420 : Nat := 118140960795 + 2700420 * 2 ^ 59
def prefixEnd_2700420 : Nat := 4983230072969 + 3 ^ 40 * 2700420 * 2
def baseEnd_2700420 : Nat := 308136317558762184006889

theorem tailTrace_2700420 : CollatzResearch.WordTrace tailWord_2700420 prefixEnd_2700420 308136317558762184006889 := by
  unfold tailWord_2700420
  simp only [CollatzResearch.WordTrace]
  refine ⟨49246204438423504931749357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65661605917898006575665809 49246204438423504931749357)
  ·
    refine ⟨18467326664408814349406009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49246204438423504931749357 18467326664408814349406009)
    ·
      refine ⟨13850494998306610762054507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18467326664408814349406009 13850494998306610762054507)
      ·
        refine ⟨20775742497459916143081761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13850494998306610762054507 20775742497459916143081761)
        ·
          refine ⟨15581806873094937107311321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20775742497459916143081761 15581806873094937107311321)
          ·
            refine ⟨11686355154821202830483491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15581806873094937107311321 11686355154821202830483491)
            ·
              refine ⟨17529532732231804245725237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11686355154821202830483491 17529532732231804245725237)
              ·
                refine ⟨1643393693646731648036741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17529532732231804245725237 1643393693646731648036741)
                ·
                  refine ⟨308136317558762184006889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1643393693646731648036741 308136317558762184006889)
                  ·
                    rfl

theorem cell22_2700420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_2700420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700420 prefixEnd_2700420 := by exact prefixLift 2700420
  have htrace : WordTrace (prefixWord ++ tailWord_2700420) baseStart_2700420 baseEnd_2700420 := by
    simpa [prefixWord, tailWord_2700420, baseEnd_2700420] using wordTrace_append hprefix tailTrace_2700420
  have hstable : (prefixWord ++ tailWord_2700420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700420).length < 2 ^ (prefixWord ++ tailWord_2700420).sum := by decide
  have hdescent : baseEnd_2700420 < baseStart_2700420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700435 : List Nat := [1, 1, 1, 2, 1, 2, 7, 2, 2, 3]
def baseStart_2700435 : Nat := 118140960795 + 2700435 * 2 ^ 59
def prefixEnd_2700435 : Nat := 4983230072969 + 3 ^ 40 * 2700435 * 2
def baseEnd_2700435 : Nat := 924414087482831512895621

theorem tailTrace_2700435 : CollatzResearch.WordTrace tailWord_2700435 prefixEnd_2700435 924414087482831512895621 := by
  unfold tailWord_2700435
  simp only [CollatzResearch.WordTrace]
  refine ⟨98492955971792667425294759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65661970647861778283529839 98492955971792667425294759)
  ·
    refine ⟨147739433957689001137942139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98492955971792667425294759 147739433957689001137942139)
    ·
      refine ⟨221609150936533501706913209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147739433957689001137942139 221609150936533501706913209)
      ·
        refine ⟨166206863202400126280184907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221609150936533501706913209 166206863202400126280184907)
        ·
          refine ⟨249310294803600189420277361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166206863202400126280184907 249310294803600189420277361)
          ·
            refine ⟨186982721102700142065208021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249310294803600189420277361 186982721102700142065208021)
            ·
              refine ⟨4382407525844534579653313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 186982721102700142065208021 4382407525844534579653313)
              ·
                refine ⟨3286805644383400934739985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4382407525844534579653313 3286805644383400934739985)
                ·
                  refine ⟨2465104233287550701054989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3286805644383400934739985 2465104233287550701054989)
                  ·
                    refine ⟨924414087482831512895621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2465104233287550701054989 924414087482831512895621)
                    ·
                      rfl

theorem cell22_2700435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 3].length) (baseStart_2700435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700435 prefixEnd_2700435 := by exact prefixLift 2700435
  have htrace : WordTrace (prefixWord ++ tailWord_2700435) baseStart_2700435 baseEnd_2700435 := by
    simpa [prefixWord, tailWord_2700435, baseEnd_2700435] using wordTrace_append hprefix tailTrace_2700435
  have hstable : (prefixWord ++ tailWord_2700435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700435).length < 2 ^ (prefixWord ++ tailWord_2700435).sum := by decide
  have hdescent : baseEnd_2700435 < baseStart_2700435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700465 : List Nat := [1, 2, 2, 5, 1, 1, 4, 6]
def baseStart_2700465 : Nat := 118140960795 + 2700465 * 2 ^ 59
def prefixEnd_2700465 : Nat := 4983230072969 + 3 ^ 40 * 2700465 * 2
def baseEnd_2700465 : Nat := 102713817455102381627281

theorem tailTrace_2700465 : CollatzResearch.WordTrace tailWord_2700465 prefixEnd_2700465 102713817455102381627281 := by
  unfold tailWord_2700465
  simp only [CollatzResearch.WordTrace]
  refine ⟨98494050161683982548886849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65662700107789321699257899 98494050161683982548886849)
  ·
    refine ⟨73870537621262986911665137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98494050161683982548886849 73870537621262986911665137)
    ·
      refine ⟨55402903215947240183748853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73870537621262986911665137 55402903215947240183748853)
      ·
        refine ⟨5194022176495053767226455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55402903215947240183748853 5194022176495053767226455)
        ·
          refine ⟨7791033264742580650839683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5194022176495053767226455 7791033264742580650839683)
          ·
            refine ⟨11686549897113870976259525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7791033264742580650839683 11686549897113870976259525)
            ·
              refine ⟨2191228105708850808048661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11686549897113870976259525 2191228105708850808048661)
              ·
                refine ⟨102713817455102381627281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2191228105708850808048661 102713817455102381627281)
                ·
                  rfl

theorem cell22_2700465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 6].length) (baseStart_2700465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700465 prefixEnd_2700465 := by exact prefixLift 2700465
  have htrace : WordTrace (prefixWord ++ tailWord_2700465) baseStart_2700465 baseEnd_2700465 := by
    simpa [prefixWord, tailWord_2700465, baseEnd_2700465] using wordTrace_append hprefix tailTrace_2700465
  have hstable : (prefixWord ++ tailWord_2700465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700465).length < 2 ^ (prefixWord ++ tailWord_2700465).sum := by decide
  have hdescent : baseEnd_2700465 < baseStart_2700465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700553 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 3, 5]
def baseStart_2700553 : Nat := 118140960795 + 2700553 * 2 ^ 59
def prefixEnd_2700553 : Nat := 4983230072969 + 3 ^ 40 * 2700553 * 2
def baseEnd_2700553 : Nat := 924454481294318538445259

theorem tailTrace_2700553 : CollatzResearch.WordTrace tailWord_2700553 prefixEnd_2700553 924454481294318538445259 := by
  unfold tailWord_2700553
  simp only [CollatzResearch.WordTrace]
  refine ⟨98497259785365173578090313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65664839856910115718726875 98497259785365173578090313)
  ·
    refine ⟨73872944839023880183567735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98497259785365173578090313 73872944839023880183567735)
    ·
      refine ⟨110809417258535820275351603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73872944839023880183567735 110809417258535820275351603)
      ·
        refine ⟨166214125887803730413027405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110809417258535820275351603 166214125887803730413027405)
        ·
          refine ⟨62330297207926398904885277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166214125887803730413027405 62330297207926398904885277)
          ·
            refine ⟨23373861452972399589331979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62330297207926398904885277 23373861452972399589331979)
            ·
              refine ⟨35060792179458599383997969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23373861452972399589331979 35060792179458599383997969)
              ·
                refine ⟨26295594134593949537998477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35060792179458599383997969 26295594134593949537998477)
                ·
                  refine ⟨9860847800472731076749429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26295594134593949537998477 9860847800472731076749429)
                  ·
                    refine ⟨924454481294318538445259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9860847800472731076749429 924454481294318538445259)
                    ·
                      rfl

theorem cell22_2700553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_2700553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700553 prefixEnd_2700553 := by exact prefixLift 2700553
  have htrace : WordTrace (prefixWord ++ tailWord_2700553) baseStart_2700553 baseEnd_2700553 := by
    simpa [prefixWord, tailWord_2700553, baseEnd_2700553] using wordTrace_append hprefix tailTrace_2700553
  have hstable : (prefixWord ++ tailWord_2700553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700553).length < 2 ^ (prefixWord ++ tailWord_2700553).sum := by decide
  have hdescent : baseEnd_2700553 < baseStart_2700553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700570 : List Nat := [3, 1, 1, 3, 3, 1, 1, 3, 1, 5]
def baseStart_2700570 : Nat := 118140960795 + 2700570 * 2 ^ 59
def prefixEnd_2700570 : Nat := 4983230072969 + 3 ^ 40 * 2700570 * 2
def baseEnd_2700570 : Nat := 924460300741736160770207

theorem tailTrace_2700570 : CollatzResearch.WordTrace tailWord_2700570 prefixEnd_2700570 924460300741736160770207 := by
  unfold tailWord_2700570
  simp only [CollatzResearch.WordTrace]
  refine ⟨24624469956575896370364791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65665253217535723654306109 24624469956575896370364791)
  ·
    refine ⟨36936704934863844555547187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24624469956575896370364791 36936704934863844555547187)
    ·
      refine ⟨55405057402295766833320781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36936704934863844555547187 55405057402295766833320781)
      ·
        refine ⟨20776896525860912562495293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55405057402295766833320781 20776896525860912562495293)
        ·
          refine ⟨7791336197197842210935735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20776896525860912562495293 7791336197197842210935735)
          ·
            refine ⟨11687004295796763316403603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7791336197197842210935735 11687004295796763316403603)
            ·
              refine ⟨17530506443695144974605405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11687004295796763316403603 17530506443695144974605405)
              ·
                refine ⟨6573939916385679365477027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17530506443695144974605405 6573939916385679365477027)
                ·
                  refine ⟨9860909874578519048215541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6573939916385679365477027 9860909874578519048215541)
                  ·
                    refine ⟨924460300741736160770207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9860909874578519048215541 924460300741736160770207)
                    ·
                      rfl

theorem cell22_2700570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_2700570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700570 prefixEnd_2700570 := by exact prefixLift 2700570
  have htrace : WordTrace (prefixWord ++ tailWord_2700570) baseStart_2700570 baseEnd_2700570 := by
    simpa [prefixWord, tailWord_2700570, baseEnd_2700570] using wordTrace_append hprefix tailTrace_2700570
  have hstable : (prefixWord ++ tailWord_2700570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700570).length < 2 ^ (prefixWord ++ tailWord_2700570).sum := by decide
  have hdescent : baseEnd_2700570 < baseStart_2700570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700589 : List Nat := [1, 5, 3, 1, 1, 1, 1, 5, 4]
def baseStart_2700589 : Nat := 118140960795 + 2700589 * 2 ^ 59
def prefixEnd_2700589 : Nat := 4983230072969 + 3 ^ 40 * 2700589 * 2
def baseEnd_2700589 : Nat := 308155601610008814848383

theorem tailTrace_2700589 : CollatzResearch.WordTrace tailWord_2700589 prefixEnd_2700589 308155601610008814848383 := by
  unfold tailWord_2700589
  simp only [CollatzResearch.WordTrace]
  refine ⟨98498572813234751726400821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65665715208823167817600547 98498572813234751726400821)
  ·
    refine ⟨9234241201240757974350077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98498572813234751726400821 9234241201240757974350077)
    ·
      refine ⟨3462840450465284240381279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9234241201240757974350077 3462840450465284240381279)
      ·
        refine ⟨5194260675697926360571919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3462840450465284240381279 5194260675697926360571919)
        ·
          refine ⟨7791391013546889540857879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5194260675697926360571919 7791391013546889540857879)
          ·
            refine ⟨11687086520320334311286819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7791391013546889540857879 11687086520320334311286819)
            ·
              refine ⟨17530629780480501466930229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11687086520320334311286819 17530629780480501466930229)
              ·
                refine ⟨1643496541920047012524709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17530629780480501466930229 1643496541920047012524709)
                ·
                  refine ⟨308155601610008814848383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1643496541920047012524709 308155601610008814848383)
                  ·
                    rfl

theorem cell22_2700589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_2700589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700589 prefixEnd_2700589 := by exact prefixLift 2700589
  have htrace : WordTrace (prefixWord ++ tailWord_2700589) baseStart_2700589 baseEnd_2700589 := by
    simpa [prefixWord, tailWord_2700589, baseEnd_2700589] using wordTrace_append hprefix tailTrace_2700589
  have hstable : (prefixWord ++ tailWord_2700589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700589).length < 2 ^ (prefixWord ++ tailWord_2700589).sum := by decide
  have hdescent : baseEnd_2700589 < baseStart_2700589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700604 : List Nat := [2, 2, 2, 2, 1, 5, 1, 2, 2, 3]
def baseStart_2700604 : Nat := 118140960795 + 2700604 * 2 ^ 59
def prefixEnd_2700604 : Nat := 4983230072969 + 3 ^ 40 * 2700604 * 2
def baseEnd_2700604 : Nat := 924471939636571405420103

theorem tailTrace_2700604 : CollatzResearch.WordTrace tailWord_2700604 prefixEnd_2700604 924471939636571405420103 := by
  unfold tailWord_2700604
  simp only [CollatzResearch.WordTrace]
  refine ⟨49249559954090204644098433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65666079938786939525464577 49249559954090204644098433)
  ·
    refine ⟨36937169965567653483073825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49249559954090204644098433 36937169965567653483073825)
    ·
      refine ⟨27702877474175740112305369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36937169965567653483073825 27702877474175740112305369)
      ·
        refine ⟨20777158105631805084229027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27702877474175740112305369 20777158105631805084229027)
        ·
          refine ⟨31165737158447707626343541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20777158105631805084229027 31165737158447707626343541)
          ·
            refine ⟨2921787858604472589969707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31165737158447707626343541 2921787858604472589969707)
            ·
              refine ⟨4382681787906708884954561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2921787858604472589969707 4382681787906708884954561)
              ·
                refine ⟨3287011340930031663715921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4382681787906708884954561 3287011340930031663715921)
                ·
                  refine ⟨2465258505697523747786941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3287011340930031663715921 2465258505697523747786941)
                  ·
                    refine ⟨924471939636571405420103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2465258505697523747786941 924471939636571405420103)
                    ·
                      rfl

theorem cell22_2700604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_2700604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700604 prefixEnd_2700604 := by exact prefixLift 2700604
  have htrace : WordTrace (prefixWord ++ tailWord_2700604) baseStart_2700604 baseEnd_2700604 := by
    simpa [prefixWord, tailWord_2700604, baseEnd_2700604] using wordTrace_append hprefix tailTrace_2700604
  have hstable : (prefixWord ++ tailWord_2700604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700604).length < 2 ^ (prefixWord ++ tailWord_2700604).sum := by decide
  have hdescent : baseEnd_2700604 < baseStart_2700604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700613 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 1, 8]
def baseStart_2700613 : Nat := 118140960795 + 2700613 * 2 ^ 59
def prefixEnd_2700613 : Nat := 4983230072969 + 3 ^ 40 * 2700613 * 2
def baseEnd_2700613 : Nat := 924475020520498381945075

theorem tailTrace_2700613 : CollatzResearch.WordTrace tailWord_2700613 prefixEnd_2700613 924475020520498381945075 := by
  unfold tailWord_2700613
  simp only [CollatzResearch.WordTrace]
  refine ⟨98499448165147803825274493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65666298776765202550182995 98499448165147803825274493)
  ·
    refine ⟨36937293061930426434477935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98499448165147803825274493 36937293061930426434477935)
    ·
      refine ⟨55405939592895639651716903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36937293061930426434477935 55405939592895639651716903)
      ·
        refine ⟨83108909389343459477575355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55405939592895639651716903 83108909389343459477575355)
        ·
          refine ⟨124663364084015189216363033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83108909389343459477575355 124663364084015189216363033)
          ·
            refine ⟨93497523063011391912272275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124663364084015189216363033 93497523063011391912272275)
            ·
              refine ⟨140246284594517087868408413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93497523063011391912272275 140246284594517087868408413)
              ·
                refine ⟨52592356722943907950653155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140246284594517087868408413 52592356722943907950653155)
                ·
                  refine ⟨78888535084415861925979733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52592356722943907950653155 78888535084415861925979733)
                  ·
                    refine ⟨924475020520498381945075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78888535084415861925979733 924475020520498381945075)
                    ·
                      rfl

theorem cell22_2700613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_2700613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700613 prefixEnd_2700613 := by exact prefixLift 2700613
  have htrace : WordTrace (prefixWord ++ tailWord_2700613) baseStart_2700613 baseEnd_2700613 := by
    simpa [prefixWord, tailWord_2700613, baseEnd_2700613] using wordTrace_append hprefix tailTrace_2700613
  have hstable : (prefixWord ++ tailWord_2700613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700613).length < 2 ^ (prefixWord ++ tailWord_2700613).sum := by decide
  have hdescent : baseEnd_2700613 < baseStart_2700613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700621 : List Nat := [1, 6, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_2700621 : Nat := 118140960795 + 2700621 * 2 ^ 59
def prefixEnd_2700621 : Nat := 4983230072969 + 3 ^ 40 * 2700621 * 2
def baseEnd_2700621 : Nat := 924477759083989027745051

theorem tailTrace_2700621 : CollatzResearch.WordTrace tailWord_2700621 prefixEnd_2700621 924477759083989027745051 := by
  unfold tailWord_2700621
  simp only [CollatzResearch.WordTrace]
  refine ⟨98499739949118821191565717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65666493299412547461043811 98499739949118821191565717)
  ·
    refine ⟨4617175310114944743354643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 98499739949118821191565717 4617175310114944743354643)
    ·
      refine ⟨6925762965172417115031965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4617175310114944743354643 6925762965172417115031965)
      ·
        refine ⟨2597161111939656418136987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6925762965172417115031965 2597161111939656418136987)
        ·
          refine ⟨3895741667909484627205481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2597161111939656418136987 3895741667909484627205481)
          ·
            refine ⟨2921806250932113470404111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3895741667909484627205481 2921806250932113470404111)
            ·
              refine ⟨4382709376398170205606167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2921806250932113470404111 4382709376398170205606167)
              ·
                refine ⟨6574064064597255308409251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4382709376398170205606167 6574064064597255308409251)
                ·
                  refine ⟨9861096096895882962613877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6574064064597255308409251 9861096096895882962613877)
                  ·
                    refine ⟨924477759083989027745051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9861096096895882962613877 924477759083989027745051)
                    ·
                      rfl

theorem cell22_2700621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_2700621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700621 prefixEnd_2700621 := by exact prefixLift 2700621
  have htrace : WordTrace (prefixWord ++ tailWord_2700621) baseStart_2700621 baseEnd_2700621 := by
    simpa [prefixWord, tailWord_2700621, baseEnd_2700621] using wordTrace_append hprefix tailTrace_2700621
  have hstable : (prefixWord ++ tailWord_2700621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700621).length < 2 ^ (prefixWord ++ tailWord_2700621).sum := by decide
  have hdescent : baseEnd_2700621 < baseStart_2700621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700679 : List Nat := [1, 1, 4, 2, 2, 4, 2, 1, 5]
def baseStart_2700679 : Nat := 118140960795 + 2700679 * 2 ^ 59
def prefixEnd_2700679 : Nat := 4983230072969 + 3 ^ 40 * 2700679 * 2
def baseEnd_2700679 : Nat := 308165871223098736598291

theorem tailTrace_2700679 : CollatzResearch.WordTrace tailWord_2700679 prefixEnd_2700679 308165871223098736598291 := by
  unfold tailWord_2700679
  simp only [CollatzResearch.WordTrace]
  refine ⟨98501855382908697097177091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65667903588605798064784727 98501855382908697097177091)
  ·
    refine ⟨147752783074363045645765637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98501855382908697097177091 147752783074363045645765637)
    ·
      refine ⟨27703646826443071058581057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147752783074363045645765637 27703646826443071058581057)
      ·
        refine ⟨20777735119832303293935793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27703646826443071058581057 20777735119832303293935793)
        ·
          refine ⟨15583301339874227470451845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20777735119832303293935793 15583301339874227470451845)
          ·
            refine ⟨2921869001226417650709721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15583301339874227470451845 2921869001226417650709721)
            ·
              refine ⟨2191401750919813238032291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2921869001226417650709721 2191401750919813238032291)
              ·
                refine ⟨3287102626379719857048437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2191401750919813238032291 3287102626379719857048437)
                ·
                  refine ⟨308165871223098736598291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3287102626379719857048437 308165871223098736598291)
                  ·
                    rfl

theorem cell22_2700679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 5].length) (baseStart_2700679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700679 prefixEnd_2700679 := by exact prefixLift 2700679
  have htrace : WordTrace (prefixWord ++ tailWord_2700679) baseStart_2700679 baseEnd_2700679 := by
    simpa [prefixWord, tailWord_2700679, baseEnd_2700679] using wordTrace_append hprefix tailTrace_2700679
  have hstable : (prefixWord ++ tailWord_2700679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700679).length < 2 ^ (prefixWord ++ tailWord_2700679).sum := by decide
  have hdescent : baseEnd_2700679 < baseStart_2700679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700707 : List Nat := [1, 1, 1, 4, 1, 3, 2, 5, 4]
def baseStart_2700707 : Nat := 118140960795 + 2700707 * 2 ^ 59
def prefixEnd_2700707 : Nat := 4983230072969 + 3 ^ 40 * 2700707 * 2
def baseEnd_2700707 : Nat := 308169066213837823364929

theorem tailTrace_2700707 : CollatzResearch.WordTrace tailWord_2700707 prefixEnd_2700707 308169066213837823364929 := by
  unfold tailWord_2700707
  simp only [CollatzResearch.WordTrace]
  refine ⟨98502876626807257879196375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65668584417871505252797583 98502876626807257879196375)
  ·
    refine ⟨147754314940210886818794563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98502876626807257879196375 147754314940210886818794563)
    ·
      refine ⟨221631472410316330228191845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147754314940210886818794563 221631472410316330228191845)
      ·
        refine ⟨41555901076934311917785971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221631472410316330228191845 41555901076934311917785971)
        ·
          refine ⟨62333851615401467876678957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41555901076934311917785971 62333851615401467876678957)
          ·
            refine ⟨23375194355775550453754609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62333851615401467876678957 23375194355775550453754609)
            ·
              refine ⟨17531395766831662840315957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23375194355775550453754609 17531395766831662840315957)
              ·
                refine ⟨1643568353140468391279621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17531395766831662840315957 1643568353140468391279621)
                ·
                  refine ⟨308169066213837823364929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1643568353140468391279621 308169066213837823364929)
                  ·
                    rfl

theorem cell22_2700707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 4].length) (baseStart_2700707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700707 prefixEnd_2700707 := by exact prefixLift 2700707
  have htrace : WordTrace (prefixWord ++ tailWord_2700707) baseStart_2700707 baseEnd_2700707 := by
    simpa [prefixWord, tailWord_2700707, baseEnd_2700707] using wordTrace_append hprefix tailTrace_2700707
  have hstable : (prefixWord ++ tailWord_2700707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700707).length < 2 ^ (prefixWord ++ tailWord_2700707).sum := by decide
  have hdescent : baseEnd_2700707 < baseStart_2700707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700720 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 4, 4]
def baseStart_2700720 : Nat := 118140960795 + 2700720 * 2 ^ 59
def prefixEnd_2700720 : Nat := 4983230072969 + 3 ^ 40 * 2700720 * 2
def baseEnd_2700720 : Nat := 924511648807185769519747

theorem tailTrace_2700720 : CollatzResearch.WordTrace tailWord_2700720 prefixEnd_2700720 924511648807185769519747 := by
  unfold tailWord_2700720
  simp only [CollatzResearch.WordTrace]
  refine ⟨49251675387880080549709807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65668900517173440732946409 49251675387880080549709807)
  ·
    refine ⟨73877513081820120824564711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49251675387880080549709807 73877513081820120824564711)
    ·
      refine ⟨110816269622730181236847067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73877513081820120824564711 110816269622730181236847067)
      ·
        refine ⟨166224404434095271855270601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110816269622730181236847067 166224404434095271855270601)
        ·
          refine ⟨124668303325571453891452951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166224404434095271855270601 124668303325571453891452951)
          ·
            refine ⟨187002454988357180837179427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124668303325571453891452951 187002454988357180837179427)
            ·
              refine ⟨280503682482535771255769141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187002454988357180837179427 280503682482535771255769141)
              ·
                refine ⟨26297220232737728555228357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 280503682482535771255769141 26297220232737728555228357)
                ·
                  refine ⟨4930728793638324104105317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26297220232737728555228357 4930728793638324104105317)
                  ·
                    refine ⟨924511648807185769519747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4930728793638324104105317 924511648807185769519747)
                    ·
                      rfl

theorem cell22_2700720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_2700720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700720 prefixEnd_2700720 := by exact prefixLift 2700720
  have htrace : WordTrace (prefixWord ++ tailWord_2700720) baseStart_2700720 baseEnd_2700720 := by
    simpa [prefixWord, tailWord_2700720, baseEnd_2700720] using wordTrace_append hprefix tailTrace_2700720
  have hstable : (prefixWord ++ tailWord_2700720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700720).length < 2 ^ (prefixWord ++ tailWord_2700720).sum := by decide
  have hdescent : baseEnd_2700720 < baseStart_2700720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700767 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 5, 3]
def baseStart_2700767 : Nat := 118140960795 + 2700767 * 2 ^ 59
def prefixEnd_2700767 : Nat := 4983230072969 + 3 ^ 40 * 2700767 * 2
def baseEnd_2700767 : Nat := 924527737867693313594603

theorem tailTrace_2700767 : CollatzResearch.WordTrace tailWord_2700767 prefixEnd_2700767 924527737867693313594603 := by
  unfold tailWord_2700767
  simp only [CollatzResearch.WordTrace]
  refine ⟨98505065006589888126380555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65670043337726592084253703 98505065006589888126380555)
  ·
    refine ⟨147757597509884832189570833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98505065006589888126380555 147757597509884832189570833)
    ·
      refine ⟨110818198132413624142178125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147757597509884832189570833 110818198132413624142178125)
      ·
        refine ⟨41556824299655109053316797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110818198132413624142178125 41556824299655109053316797)
        ·
          refine ⟨15583809112370665894993799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41556824299655109053316797 15583809112370665894993799)
          ·
            refine ⟨23375713668555998842490699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15583809112370665894993799 23375713668555998842490699)
            ·
              refine ⟨35063570502833998263736049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23375713668555998842490699 35063570502833998263736049)
              ·
                refine ⟨26297677877125498697802037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35063570502833998263736049 26297677877125498697802037)
                ·
                  refine ⟨2465407300980515502918941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26297677877125498697802037 2465407300980515502918941)
                  ·
                    refine ⟨924527737867693313594603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2465407300980515502918941 924527737867693313594603)
                    ·
                      rfl

theorem cell22_2700767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 3].length) (baseStart_2700767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700767 prefixEnd_2700767 := by exact prefixLift 2700767
  have htrace : WordTrace (prefixWord ++ tailWord_2700767) baseStart_2700767 baseEnd_2700767 := by
    simpa [prefixWord, tailWord_2700767, baseEnd_2700767] using wordTrace_append hprefix tailTrace_2700767
  have hstable : (prefixWord ++ tailWord_2700767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700767).length < 2 ^ (prefixWord ++ tailWord_2700767).sum := by decide
  have hdescent : baseEnd_2700767 < baseStart_2700767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700784 : List Nat := [2, 1, 1, 1, 3, 5, 2, 1, 3, 3]
def baseStart_2700784 : Nat := 118140960795 + 2700784 * 2 ^ 59
def prefixEnd_2700784 : Nat := 4983230072969 + 3 ^ 40 * 2700784 * 2
def baseEnd_2700784 : Nat := 924533557315110935919551

theorem tailTrace_2700784 : CollatzResearch.WordTrace tailWord_2700784 prefixEnd_2700784 924533557315110935919551 := by
  unfold tailWord_2700784
  simp only [CollatzResearch.WordTrace]
  refine ⟨49252842523764150014874703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65670456698352200019832937 49252842523764150014874703)
  ·
    refine ⟨73879263785646225022312055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49252842523764150014874703 73879263785646225022312055)
    ·
      refine ⟨110818895678469337533468083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73879263785646225022312055 110818895678469337533468083)
      ·
        refine ⟨166228343517704006300202125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110818895678469337533468083 166228343517704006300202125)
        ·
          refine ⟨62335628819139002362575797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166228343517704006300202125 62335628819139002362575797)
          ·
            refine ⟨5843965201794281471491481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62335628819139002362575797 5843965201794281471491481)
            ·
              refine ⟨4382973901345711103618611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5843965201794281471491481 4382973901345711103618611)
              ·
                refine ⟨6574460852018566655427917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4382973901345711103618611 6574460852018566655427917)
                ·
                  refine ⟨2465422819506962495785469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6574460852018566655427917 2465422819506962495785469)
                  ·
                    refine ⟨924533557315110935919551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2465422819506962495785469 924533557315110935919551)
                    ·
                      rfl

theorem cell22_2700784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 3, 3].length) (baseStart_2700784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700784 prefixEnd_2700784 := by exact prefixLift 2700784
  have htrace : WordTrace (prefixWord ++ tailWord_2700784) baseStart_2700784 baseEnd_2700784 := by
    simpa [prefixWord, tailWord_2700784, baseEnd_2700784] using wordTrace_append hprefix tailTrace_2700784
  have hstable : (prefixWord ++ tailWord_2700784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700784).length < 2 ^ (prefixWord ++ tailWord_2700784).sum := by decide
  have hdescent : baseEnd_2700784 < baseStart_2700784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700886 : List Nat := [5, 2, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_2700886 : Nat := 118140960795 + 2700886 * 2 ^ 59
def prefixEnd_2700886 : Nat := 4983230072969 + 3 ^ 40 * 2700886 * 2
def baseEnd_2700886 : Nat := 924568473999616669869239

theorem tailTrace_2700886 : CollatzResearch.WordTrace tailWord_2700886 prefixEnd_2700886 924568473999616669869239 := by
  unfold tailWord_2700886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6156837830822423215622657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65672936862105847633308341 6156837830822423215622657)
  ·
    refine ⟨4617628373116817411716993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6156837830822423215622657 4617628373116817411716993)
    ·
      refine ⟨3463221279837613058787745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4617628373116817411716993 3463221279837613058787745)
      ·
        refine ⟨2597415959878209794090809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3463221279837613058787745 2597415959878209794090809)
        ·
          refine ⟨1948061969908657345568107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2597415959878209794090809 1948061969908657345568107)
          ·
            refine ⟨2922092954862986018352161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1948061969908657345568107 2922092954862986018352161)
            ·
              refine ⟨2191569716147239513764121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2922092954862986018352161 2191569716147239513764121)
              ·
                refine ⟨1643677287110429635323091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2191569716147239513764121 1643677287110429635323091)
                ·
                  refine ⟨2465515930665644452984637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643677287110429635323091 2465515930665644452984637)
                  ·
                    refine ⟨924568473999616669869239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2465515930665644452984637 924568473999616669869239)
                    ·
                      rfl

theorem cell22_2700886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_2700886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700886 prefixEnd_2700886 := by exact prefixLift 2700886
  have htrace : WordTrace (prefixWord ++ tailWord_2700886) baseStart_2700886 baseEnd_2700886 := by
    simpa [prefixWord, tailWord_2700886, baseEnd_2700886] using wordTrace_append hprefix tailTrace_2700886
  have hstable : (prefixWord ++ tailWord_2700886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700886).length < 2 ^ (prefixWord ++ tailWord_2700886).sum := by decide
  have hdescent : baseEnd_2700886 < baseStart_2700886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700904 : List Nat := [2, 1, 4, 3, 1, 1, 3, 7]
def baseStart_2700904 : Nat := 118140960795 + 2700904 * 2 ^ 59
def prefixEnd_2700904 : Nat := 4983230072969 + 3 ^ 40 * 2700904 * 2
def baseEnd_2700904 : Nat := 102730515085274513657687

theorem tailTrace_2700904 : CollatzResearch.WordTrace tailWord_2700904 prefixEnd_2700904 102730515085274513657687 := by
  unfold tailWord_2700904
  simp only [CollatzResearch.WordTrace]
  refine ⟨49255030903546780262058883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65673374538062373682745177 49255030903546780262058883)
  ·
    refine ⟨73882546355320170393088325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49255030903546780262058883 73882546355320170393088325)
    ·
      refine ⟨13852977441622531948704061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73882546355320170393088325 13852977441622531948704061)
      ·
        refine ⟨5194866540608449480764023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13852977441622531948704061 5194866540608449480764023)
        ·
          refine ⟨7792299810912674221146035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5194866540608449480764023 7792299810912674221146035)
          ·
            refine ⟨11688449716369011331719053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7792299810912674221146035 11688449716369011331719053)
            ·
              refine ⟨4383168643638379249394645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11688449716369011331719053 4383168643638379249394645)
              ·
                refine ⟨102730515085274513657687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4383168643638379249394645 102730515085274513657687)
                ·
                  rfl

theorem cell22_2700904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 7].length) (baseStart_2700904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700904 prefixEnd_2700904 := by exact prefixLift 2700904
  have htrace : WordTrace (prefixWord ++ tailWord_2700904) baseStart_2700904 baseEnd_2700904 := by
    simpa [prefixWord, tailWord_2700904, baseEnd_2700904] using wordTrace_append hprefix tailTrace_2700904
  have hstable : (prefixWord ++ tailWord_2700904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700904).length < 2 ^ (prefixWord ++ tailWord_2700904).sum := by decide
  have hdescent : baseEnd_2700904 < baseStart_2700904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700964 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_2700964 : Nat := 118140960795 + 2700964 * 2 ^ 59
def prefixEnd_2700964 : Nat := 4983230072969 + 3 ^ 40 * 2700964 * 2
def baseEnd_2700964 : Nat := 924595174993650466418999

theorem tailTrace_2700964 : CollatzResearch.WordTrace tailWord_2700964 prefixEnd_2700964 924595174993650466418999 := by
  unfold tailWord_2700964
  simp only [CollatzResearch.WordTrace]
  refine ⟨49256125093438095385650973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65674833457917460514201297 49256125093438095385650973)
  ·
    refine ⟨18471046910039285769619115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49256125093438095385650973 18471046910039285769619115)
    ·
      refine ⟨27706570365058928654428673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18471046910039285769619115 27706570365058928654428673)
      ·
        refine ⟨20779927773794196490821505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27706570365058928654428673 20779927773794196490821505)
        ·
          refine ⟨15584945830345647368116129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20779927773794196490821505 15584945830345647368116129)
          ·
            refine ⟨11688709372759235526087097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15584945830345647368116129 11688709372759235526087097)
            ·
              refine ⟨8766532029569426644565323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11688709372759235526087097 8766532029569426644565323)
              ·
                refine ⟨13149798044354139966847985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8766532029569426644565323 13149798044354139966847985)
                ·
                  refine ⟨9862348533265604975135989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13149798044354139966847985 9862348533265604975135989)
                  ·
                    refine ⟨924595174993650466418999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9862348533265604975135989 924595174993650466418999)
                    ·
                      rfl

theorem cell22_2700964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_2700964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700964 prefixEnd_2700964 := by exact prefixLift 2700964
  have htrace : WordTrace (prefixWord ++ tailWord_2700964) baseStart_2700964 baseEnd_2700964 := by
    simpa [prefixWord, tailWord_2700964, baseEnd_2700964] using wordTrace_append hprefix tailTrace_2700964
  have hstable : (prefixWord ++ tailWord_2700964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700964).length < 2 ^ (prefixWord ++ tailWord_2700964).sum := by decide
  have hdescent : baseEnd_2700964 < baseStart_2700964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2700996 : List Nat := [2, 3, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_2700996 : Nat := 118140960795 + 2700996 * 2 ^ 59
def prefixEnd_2700996 : Nat := 4983230072969 + 3 ^ 40 * 2700996 * 2
def baseEnd_2700996 : Nat := 924606129247613049618901

theorem tailTrace_2700996 : CollatzResearch.WordTrace tailWord_2700996 prefixEnd_2700996 924606129247613049618901 := by
  unfold tailWord_2700996
  simp only [CollatzResearch.WordTrace]
  refine ⟨49256708661380130118233421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65675611548506840157644561 49256708661380130118233421)
  ·
    refine ⟨18471265748017548794337533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49256708661380130118233421 18471265748017548794337533)
    ·
      refine ⟨6926724655506580797876575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18471265748017548794337533 6926724655506580797876575)
      ·
        refine ⟨10390086983259871196814863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6926724655506580797876575 10390086983259871196814863)
        ·
          refine ⟨15585130474889806795222295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10390086983259871196814863 15585130474889806795222295)
          ·
            refine ⟨23377695712334710192833443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15585130474889806795222295 23377695712334710192833443)
            ·
              refine ⟨35066543568502065289250165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23377695712334710192833443 35066543568502065289250165)
              ·
                refine ⟨3287488459547068620867203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35066543568502065289250165 3287488459547068620867203)
                ·
                  refine ⟨4931232689320602931300805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3287488459547068620867203 4931232689320602931300805)
                  ·
                    refine ⟨924606129247613049618901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4931232689320602931300805 924606129247613049618901)
                    ·
                      rfl

theorem cell22_2700996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_2700996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2700996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2700996 prefixEnd_2700996 := by exact prefixLift 2700996
  have htrace : WordTrace (prefixWord ++ tailWord_2700996) baseStart_2700996 baseEnd_2700996 := by
    simpa [prefixWord, tailWord_2700996, baseEnd_2700996] using wordTrace_append hprefix tailTrace_2700996
  have hstable : (prefixWord ++ tailWord_2700996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2700996).length < 2 ^ (prefixWord ++ tailWord_2700996).sum := by decide
  have hdescent : baseEnd_2700996 < baseStart_2700996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2700996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701041 : List Nat := [1, 2, 2, 2, 2, 4, 2, 1, 2, 4]
def baseStart_2701041 : Nat := 118140960795 + 2701041 * 2 ^ 59
def prefixEnd_2701041 : Nat := 4983230072969 + 3 ^ 40 * 2701041 * 2
def baseEnd_2701041 : Nat := 924621533667247932243763

theorem tailTrace_2701041 : CollatzResearch.WordTrace tailWord_2701041 prefixEnd_2701041 924621533667247932243763 := by
  unfold tailWord_2701041
  simp only [CollatzResearch.WordTrace]
  refine ⟨98515058607597232921854977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65676705738398155281236651 98515058607597232921854977)
  ·
    refine ⟨73886293955697924691391233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98515058607597232921854977 73886293955697924691391233)
    ·
      refine ⟨55414720466773443518543425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73886293955697924691391233 55414720466773443518543425)
      ·
        refine ⟨41561040350080082638907569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55414720466773443518543425 41561040350080082638907569)
        ·
          refine ⟨31170780262560061979180677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41561040350080082638907569 31170780262560061979180677)
          ·
            refine ⟨5844521299230011621096377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31170780262560061979180677 5844521299230011621096377)
            ·
              refine ⟨4383390974422508715822283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5844521299230011621096377 4383390974422508715822283)
              ·
                refine ⟨6575086461633763073733425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4383390974422508715822283 6575086461633763073733425)
                ·
                  refine ⟨4931314846225322305300069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6575086461633763073733425 4931314846225322305300069)
                  ·
                    refine ⟨924621533667247932243763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4931314846225322305300069 924621533667247932243763)
                    ·
                      rfl

theorem cell22_2701041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_2701041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701041 prefixEnd_2701041 := by exact prefixLift 2701041
  have htrace : WordTrace (prefixWord ++ tailWord_2701041) baseStart_2701041 baseEnd_2701041 := by
    simpa [prefixWord, tailWord_2701041, baseEnd_2701041] using wordTrace_append hprefix tailTrace_2701041
  have hstable : (prefixWord ++ tailWord_2701041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701041).length < 2 ^ (prefixWord ++ tailWord_2701041).sum := by decide
  have hdescent : baseEnd_2701041 < baseStart_2701041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701105 : List Nat := [1, 2, 2, 3, 2, 3, 2, 3, 1, 3]
def baseStart_2701105 : Nat := 118140960795 + 2701105 * 2 ^ 59
def prefixEnd_2701105 : Nat := 4983230072969 + 3 ^ 40 * 2701105 * 2
def baseEnd_2701105 : Nat := 924643442175173098643567

theorem tailTrace_2701105 : CollatzResearch.WordTrace tailWord_2701105 prefixEnd_2701105 924643442175173098643567 := by
  unfold tailWord_2701105
  simp only [CollatzResearch.WordTrace]
  refine ⟨98517392879365371852184769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65678261919576914568123179 98517392879365371852184769)
  ·
    refine ⟨73888044659524028889138577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98517392879365371852184769 73888044659524028889138577)
    ·
      refine ⟨55416033494643021666853933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73888044659524028889138577 55416033494643021666853933)
      ·
        refine ⟨20781012560491133125070225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55416033494643021666853933 20781012560491133125070225)
        ·
          refine ⟨15585759420368349843802669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20781012560491133125070225 15585759420368349843802669)
          ·
            refine ⟨5844659782638131191426001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15585759420368349843802669 5844659782638131191426001)
            ·
              refine ⟨4383494836978598393569501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5844659782638131191426001 4383494836978598393569501)
              ·
                refine ⟨1643810563866974397588563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4383494836978598393569501 1643810563866974397588563)
                ·
                  refine ⟨2465715845800461596382845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643810563866974397588563 2465715845800461596382845)
                  ·
                    refine ⟨924643442175173098643567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2465715845800461596382845 924643442175173098643567)
                    ·
                      rfl

theorem cell22_2701105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 1, 3].length) (baseStart_2701105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701105 prefixEnd_2701105 := by exact prefixLift 2701105
  have htrace : WordTrace (prefixWord ++ tailWord_2701105) baseStart_2701105 baseEnd_2701105 := by
    simpa [prefixWord, tailWord_2701105, baseEnd_2701105] using wordTrace_append hprefix tailTrace_2701105
  have hstable : (prefixWord ++ tailWord_2701105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701105).length < 2 ^ (prefixWord ++ tailWord_2701105).sum := by decide
  have hdescent : baseEnd_2701105 < baseStart_2701105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701118 : List Nat := [4, 2, 1, 2, 2, 1, 3, 2, 5]
def baseStart_2701118 : Nat := 118140960795 + 2701118 * 2 ^ 59
def prefixEnd_2701118 : Nat := 4983230072969 + 3 ^ 40 * 2701118 * 2
def baseEnd_2701118 : Nat := 308215964113615132689509

theorem tailTrace_2701118 : CollatzResearch.WordTrace tailWord_2701118 prefixEnd_2701118 308215964113615132689509 := by
  unfold tailWord_2701118
  simp only [CollatzResearch.WordTrace]
  refine ⟨12314733378539784384051001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65678578018878850048272005 12314733378539784384051001)
  ·
    refine ⟨9236050033904838288038251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12314733378539784384051001 9236050033904838288038251)
    ·
      refine ⟨13854075050857257432057377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9236050033904838288038251 13854075050857257432057377)
      ·
        refine ⟨10390556288142943074043033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13854075050857257432057377 10390556288142943074043033)
        ·
          refine ⟨7792917216107207305532275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10390556288142943074043033 7792917216107207305532275)
          ·
            refine ⟨11689375824160810958298413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7792917216107207305532275 11689375824160810958298413)
            ·
              refine ⟨4383515934060304109361905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11689375824160810958298413 4383515934060304109361905)
              ·
                refine ⟨3287636950545228082021429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4383515934060304109361905 3287636950545228082021429)
                ·
                  refine ⟨308215964113615132689509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3287636950545228082021429 308215964113615132689509)
                  ·
                    rfl

theorem cell22_2701118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_2701118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701118 prefixEnd_2701118 := by exact prefixLift 2701118
  have htrace : WordTrace (prefixWord ++ tailWord_2701118) baseStart_2701118 baseEnd_2701118 := by
    simpa [prefixWord, tailWord_2701118, baseEnd_2701118] using wordTrace_append hprefix tailTrace_2701118
  have hstable : (prefixWord ++ tailWord_2701118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701118).length < 2 ^ (prefixWord ++ tailWord_2701118).sum := by decide
  have hdescent : baseEnd_2701118 < baseStart_2701118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701133 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_2701133 : Nat := 118140960795 + 2701133 * 2 ^ 59
def prefixEnd_2701133 : Nat := 4983230072969 + 3 ^ 40 * 2701133 * 2
def baseEnd_2701133 : Nat := 924653027147390358943481

theorem tailTrace_2701133 : CollatzResearch.WordTrace tailWord_2701133 prefixEnd_2701133 924653027147390358943481 := by
  unfold tailWord_2701133
  simp only [CollatzResearch.WordTrace]
  refine ⟨98518414123263932634204053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65678942748842621756136035 98518414123263932634204053)
  ·
    refine ⟨4618050662027996842228315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 98518414123263932634204053 4618050662027996842228315)
    ·
      refine ⟨6927075993041995263342473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4618050662027996842228315 6927075993041995263342473)
      ·
        refine ⟨5195306994781496447506855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6927075993041995263342473 5195306994781496447506855)
        ·
          refine ⟨7792960492172244671260283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5195306994781496447506855 7792960492172244671260283)
          ·
            refine ⟨11689440738258367006890425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7792960492172244671260283 11689440738258367006890425)
            ·
              refine ⟨8767080553693775255167819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11689440738258367006890425 8767080553693775255167819)
              ·
                refine ⟨13150620830540662882751729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8767080553693775255167819 13150620830540662882751729)
                ·
                  refine ⟨9862965622905497162063797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13150620830540662882751729 9862965622905497162063797)
                  ·
                    refine ⟨924653027147390358943481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9862965622905497162063797 924653027147390358943481)
                    ·
                      rfl

theorem cell22_2701133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_2701133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701133 prefixEnd_2701133 := by exact prefixLift 2701133
  have htrace : WordTrace (prefixWord ++ tailWord_2701133) baseStart_2701133 baseEnd_2701133 := by
    simpa [prefixWord, tailWord_2701133, baseEnd_2701133] using wordTrace_append hprefix tailTrace_2701133
  have hstable : (prefixWord ++ tailWord_2701133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701133).length < 2 ^ (prefixWord ++ tailWord_2701133).sum := by decide
  have hdescent : baseEnd_2701133 < baseStart_2701133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701240 : List Nat := [2, 1, 2, 1, 2, 3, 3, 4, 1, 3]
def baseStart_2701240 : Nat := 118140960795 + 2701240 * 2 ^ 59
def prefixEnd_2701240 : Nat := 4983230072969 + 3 ^ 40 * 2701240 * 2
def baseEnd_2701240 : Nat := 924689655434077746518153

theorem tailTrace_2701240 : CollatzResearch.WordTrace tailWord_2701240 prefixEnd_2701240 924689655434077746518153 := by
  unfold tailWord_2701240
  simp only [CollatzResearch.WordTrace]
  refine ⟨49261158366938144954174587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65681544489250859938899449 49261158366938144954174587)
  ·
    refine ⟨73891737550407217431261881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49261158366938144954174587 73891737550407217431261881)
    ·
      refine ⟨55418803162805413073446411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73891737550407217431261881 55418803162805413073446411)
      ·
        refine ⟨83128204744208119610169617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55418803162805413073446411 83128204744208119610169617)
        ·
          refine ⟨62346153558156089707627213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83128204744208119610169617 62346153558156089707627213)
          ·
            refine ⟨23379807584308533640360205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62346153558156089707627213 23379807584308533640360205)
            ·
              refine ⟨8767427844115700115135077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23379807584308533640360205 8767427844115700115135077)
              ·
                refine ⟨1643892720771693771587827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8767427844115700115135077 1643892720771693771587827)
                ·
                  refine ⟨2465839081157540657381741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643892720771693771587827 2465839081157540657381741)
                  ·
                    refine ⟨924689655434077746518153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2465839081157540657381741 924689655434077746518153)
                    ·
                      rfl

theorem cell22_2701240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 1, 3].length) (baseStart_2701240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701240 prefixEnd_2701240 := by exact prefixLift 2701240
  have htrace : WordTrace (prefixWord ++ tailWord_2701240) baseStart_2701240 baseEnd_2701240 := by
    simpa [prefixWord, tailWord_2701240, baseEnd_2701240] using wordTrace_append hprefix tailTrace_2701240
  have hstable : (prefixWord ++ tailWord_2701240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701240).length < 2 ^ (prefixWord ++ tailWord_2701240).sum := by decide
  have hdescent : baseEnd_2701240 < baseStart_2701240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701287 : List Nat := [1, 1, 5, 2, 4, 1, 1, 2, 5]
def baseStart_2701287 : Nat := 118140960795 + 2701287 * 2 ^ 59
def prefixEnd_2701287 : Nat := 4983230072969 + 3 ^ 40 * 2701287 * 2
def baseEnd_2701287 : Nat := 308235248164861763531003

theorem tailTrace_2701287 : CollatzResearch.WordTrace tailWord_2701287 prefixEnd_2701287 308235248164861763531003 := by
  unfold tailWord_2701287
  simp only [CollatzResearch.WordTrace]
  refine ⟨98524030964706016935310115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65682687309804011290206743 98524030964706016935310115)
  ·
    refine ⟨147786046447059025402965173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98524030964706016935310115 147786046447059025402965173)
    ·
      refine ⟨13854941854411783631527985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147786046447059025402965173 13854941854411783631527985)
      ·
        refine ⟨10391206390808837723645989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13854941854411783631527985 10391206390808837723645989)
        ·
          refine ⟨1948351198276657073183623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10391206390808837723645989 1948351198276657073183623)
          ·
            refine ⟨2922526797414985609775435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1948351198276657073183623 2922526797414985609775435)
            ·
              refine ⟨4383790196122478414663153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2922526797414985609775435 4383790196122478414663153)
              ·
                refine ⟨3287842647091858810997365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4383790196122478414663153 3287842647091858810997365)
                ·
                  refine ⟨308235248164861763531003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3287842647091858810997365 308235248164861763531003)
                  ·
                    rfl

theorem cell22_2701287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 5].length) (baseStart_2701287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701287 prefixEnd_2701287 := by exact prefixLift 2701287
  have htrace : WordTrace (prefixWord ++ tailWord_2701287) baseStart_2701287 baseEnd_2701287 := by
    simpa [prefixWord, tailWord_2701287, baseEnd_2701287] using wordTrace_append hprefix tailTrace_2701287
  have hstable : (prefixWord ++ tailWord_2701287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701287).length < 2 ^ (prefixWord ++ tailWord_2701287).sum := by decide
  have hdescent : baseEnd_2701287 < baseStart_2701287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701296 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 3, 5]
def baseStart_2701296 : Nat := 118140960795 + 2701296 * 2 ^ 59
def prefixEnd_2701296 : Nat := 4983230072969 + 3 ^ 40 * 2701296 * 2
def baseEnd_2701296 : Nat := 924708825378512267117981

theorem tailTrace_2701296 : CollatzResearch.WordTrace tailWord_2701296 prefixEnd_2701296 924708825378512267117981 := by
  unfold tailWord_2701296
  simp only [CollatzResearch.WordTrace]
  refine ⟨49262179610836705736193871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65682906147782274314925161 49262179610836705736193871)
  ·
    refine ⟨73893269416255058604290807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49262179610836705736193871 73893269416255058604290807)
    ·
      refine ⟨110839904124382587906436211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73893269416255058604290807 110839904124382587906436211)
      ·
        refine ⟨166259856186573881859654317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110839904124382587906436211 166259856186573881859654317)
        ·
          refine ⟨62347446069965205697370369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166259856186573881859654317 62347446069965205697370369)
          ·
            refine ⟨46760584552473904273027777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62347446069965205697370369 46760584552473904273027777)
            ·
              refine ⟨35070438414355428204770833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46760584552473904273027777 35070438414355428204770833)
              ·
                refine ⟨26302828810766571153578125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35070438414355428204770833 26302828810766571153578125)
                ·
                  refine ⟨9863560804037464182591797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26302828810766571153578125 9863560804037464182591797)
                  ·
                    refine ⟨924708825378512267117981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9863560804037464182591797 924708825378512267117981)
                    ·
                      rfl

theorem cell22_2701296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_2701296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701296 prefixEnd_2701296 := by exact prefixLift 2701296
  have htrace : WordTrace (prefixWord ++ tailWord_2701296) baseStart_2701296 baseEnd_2701296 := by
    simpa [prefixWord, tailWord_2701296, baseEnd_2701296] using wordTrace_append hprefix tailTrace_2701296
  have hstable : (prefixWord ++ tailWord_2701296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701296).length < 2 ^ (prefixWord ++ tailWord_2701296).sum := by decide
  have hdescent : baseEnd_2701296 < baseStart_2701296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701325 : List Nat := [1, 7, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_2701325 : Nat := 118140960795 + 2701325 * 2 ^ 59
def prefixEnd_2701325 : Nat := 4983230072969 + 3 ^ 40 * 2701325 * 2
def baseEnd_2701325 : Nat := 924718752671165858142893

theorem tailTrace_2701325 : CollatzResearch.WordTrace tailWord_2701325 prefixEnd_2701325 924718752671165858142893 := by
  unfold tailWord_2701325
  simp only [CollatzResearch.WordTrace]
  refine ⟨98525416938568349425193429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65683611292378899616795619 98525416938568349425193429)
  ·
    refine ⟨2309189459497695689652971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 98525416938568349425193429 2309189459497695689652971)
    ·
      refine ⟨3463784189246543534479457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2309189459497695689652971 3463784189246543534479457)
      ·
        refine ⟨2597838141934907650859593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3463784189246543534479457 2597838141934907650859593)
        ·
          refine ⟨1948378606451180738144695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2597838141934907650859593 1948378606451180738144695)
          ·
            refine ⟨2922567909676771107217043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1948378606451180738144695 2922567909676771107217043)
            ·
              refine ⟨4383851864515156660825565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2922567909676771107217043 4383851864515156660825565)
              ·
                refine ⟨1643944449193183747809587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4383851864515156660825565 1643944449193183747809587)
                ·
                  refine ⟨2465916673789775621714381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643944449193183747809587 2465916673789775621714381)
                  ·
                    refine ⟨924718752671165858142893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2465916673789775621714381 924718752671165858142893)
                    ·
                      rfl

theorem cell22_2701325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_2701325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701325 prefixEnd_2701325 := by exact prefixLift 2701325
  have htrace : WordTrace (prefixWord ++ tailWord_2701325) baseStart_2701325 baseEnd_2701325 := by
    simpa [prefixWord, tailWord_2701325, baseEnd_2701325] using wordTrace_append hprefix tailTrace_2701325
  have hstable : (prefixWord ++ tailWord_2701325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701325).length < 2 ^ (prefixWord ++ tailWord_2701325).sum := by decide
  have hdescent : baseEnd_2701325 < baseStart_2701325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701345 : List Nat := [1, 2, 3, 2, 4, 1, 1, 2, 2, 4]
def baseStart_2701345 : Nat := 118140960795 + 2701345 * 2 ^ 59
def prefixEnd_2701345 : Nat := 4983230072969 + 3 ^ 40 * 2701345 * 2
def baseEnd_2701345 : Nat := 924725599079892472642831

theorem tailTrace_2701345 : CollatzResearch.WordTrace tailWord_2701345 prefixEnd_2701345 924725599079892472642831 := by
  unfold tailWord_2701345
  simp only [CollatzResearch.WordTrace]
  refine ⟨98526146398495892840921489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65684097598997261893947659 98526146398495892840921489)
  ·
    refine ⟨73894609798871919630691117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98526146398495892840921489 73894609798871919630691117)
    ·
      refine ⟨27710478674576969861509169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73894609798871919630691117 27710478674576969861509169)
      ·
        refine ⟨20782859005932727396131877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27710478674576969861509169 20782859005932727396131877)
        ·
          refine ⟨3896786063612386386774727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20782859005932727396131877 3896786063612386386774727)
          ·
            refine ⟨5845179095418579580162091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3896786063612386386774727 5845179095418579580162091)
            ·
              refine ⟨8767768643127869370243137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5845179095418579580162091 8767768643127869370243137)
              ·
                refine ⟨6575826482345902027682353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8767768643127869370243137 6575826482345902027682353)
                ·
                  refine ⟨4931869861759426520761765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6575826482345902027682353 4931869861759426520761765)
                  ·
                    refine ⟨924725599079892472642831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4931869861759426520761765 924725599079892472642831)
                    ·
                      rfl

theorem cell22_2701345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_2701345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701345 prefixEnd_2701345 := by exact prefixLift 2701345
  have htrace : WordTrace (prefixWord ++ tailWord_2701345) baseStart_2701345 baseEnd_2701345 := by
    simpa [prefixWord, tailWord_2701345, baseEnd_2701345] using wordTrace_append hprefix tailTrace_2701345
  have hstable : (prefixWord ++ tailWord_2701345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701345).length < 2 ^ (prefixWord ++ tailWord_2701345).sum := by decide
  have hdescent : baseEnd_2701345 < baseStart_2701345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701364 : List Nat := [2, 5, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_2701364 : Nat := 118140960795 + 2701364 * 2 ^ 59
def prefixEnd_2701364 : Nat := 4983230072969 + 3 ^ 40 * 2701364 * 2
def baseEnd_2701364 : Nat := 924732103168182756417773

theorem tailTrace_2701364 : CollatzResearch.WordTrace tailWord_2701364 prefixEnd_2701364 924732103168182756417773 := by
  unfold tailWord_2701364
  simp only [CollatzResearch.WordTrace]
  refine ⟨49263419692713529542931573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65684559590284706057242097 49263419692713529542931573)
  ·
    refine ⟨4618445596191893394649835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49263419692713529542931573 4618445596191893394649835)
    ·
      refine ⟨6927668394287840091974753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4618445596191893394649835 6927668394287840091974753)
      ·
        refine ⟨5195751295715880068981065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6927668394287840091974753 5195751295715880068981065)
        ·
          refine ⟨3896813471786910051735799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5195751295715880068981065 3896813471786910051735799)
          ·
            refine ⟨5845220207680365077603699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3896813471786910051735799 5845220207680365077603699)
            ·
              refine ⟨8767830311520547616405549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5845220207680365077603699 8767830311520547616405549)
              ·
                refine ⟨3287936366820205356152081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8767830311520547616405549 3287936366820205356152081)
                ·
                  refine ⟨2465952275115154017114061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3287936366820205356152081 2465952275115154017114061)
                  ·
                    refine ⟨924732103168182756417773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2465952275115154017114061 924732103168182756417773)
                    ·
                      rfl

theorem cell22_2701364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_2701364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701364 prefixEnd_2701364 := by exact prefixLift 2701364
  have htrace : WordTrace (prefixWord ++ tailWord_2701364) baseStart_2701364 baseEnd_2701364 := by
    simpa [prefixWord, tailWord_2701364, baseEnd_2701364] using wordTrace_append hprefix tailTrace_2701364
  have hstable : (prefixWord ++ tailWord_2701364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701364).length < 2 ^ (prefixWord ++ tailWord_2701364).sum := by decide
  have hdescent : baseEnd_2701364 < baseStart_2701364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701433 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 8]
def baseStart_2701433 : Nat := 118140960795 + 2701433 * 2 ^ 59
def prefixEnd_2701433 : Nat := 4983230072969 + 3 ^ 40 * 2701433 * 2
def baseEnd_2701433 : Nat := 308251907759429858814187

theorem tailTrace_2701433 : CollatzResearch.WordTrace tailWord_2701433 prefixEnd_2701433 308251907759429858814187 := by
  unfold tailWord_2701433
  simp only [CollatzResearch.WordTrace]
  refine ⟨98529356022177083870124953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65686237348118055913416635 98529356022177083870124953)
  ·
    refine ⟨73897017016632812902593715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98529356022177083870124953 73897017016632812902593715)
    ·
      refine ⟨110845525524949219353890573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73897017016632812902593715 110845525524949219353890573)
      ·
        refine ⟨41567072071855957257708965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110845525524949219353890573 41567072071855957257708965)
        ·
          refine ⟨7793826013472991985820431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41567072071855957257708965 7793826013472991985820431)
          ·
            refine ⟨11690739020209487978730647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7793826013472991985820431 11690739020209487978730647)
            ·
              refine ⟨17536108530314231968095971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11690739020209487978730647 17536108530314231968095971)
              ·
                refine ⟨26304162795471347952143957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17536108530314231968095971 26304162795471347952143957)
                ·
                  refine ⟨308251907759429858814187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26304162795471347952143957 308251907759429858814187)
                  ·
                    rfl

theorem cell22_2701433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 8].length) (baseStart_2701433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701433 prefixEnd_2701433 := by exact prefixLift 2701433
  have htrace : WordTrace (prefixWord ++ tailWord_2701433) baseStart_2701433 baseEnd_2701433 := by
    simpa [prefixWord, tailWord_2701433, baseEnd_2701433] using wordTrace_append hprefix tailTrace_2701433
  have hstable : (prefixWord ++ tailWord_2701433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701433).length < 2 ^ (prefixWord ++ tailWord_2701433).sum := by decide
  have hdescent : baseEnd_2701433 < baseStart_2701433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701486 : List Nat := [4, 1, 4, 2, 1, 1, 2, 2, 1, 4]
def baseStart_2701486 : Nat := 118140960795 + 2701486 * 2 ^ 59
def prefixEnd_2701486 : Nat := 4983230072969 + 3 ^ 40 * 2701486 * 2
def baseEnd_2701486 : Nat := 924773866261415104867399

theorem tailTrace_2701486 : CollatzResearch.WordTrace tailWord_2701486 prefixEnd_2701486 924773866261415104867399 := by
  unfold tailWord_2701486
  simp only [CollatzResearch.WordTrace]
  refine ⟨12316411136373134240225539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65687526060656715947869541 12316411136373134240225539)
  ·
    refine ⟨18474616704559701360338309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12316411136373134240225539 18474616704559701360338309)
    ·
      refine ⟨3463990632104944005063433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18474616704559701360338309 3463990632104944005063433)
      ·
        refine ⟨2597992974078708003797575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3463990632104944005063433 2597992974078708003797575)
        ·
          refine ⟨3896989461118062005696363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2597992974078708003797575 3896989461118062005696363)
          ·
            refine ⟨5845484191677093008544545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3896989461118062005696363 5845484191677093008544545)
            ·
              refine ⟨4384113143757819756408409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5845484191677093008544545 4384113143757819756408409)
              ·
                refine ⟨3288084857818364817306307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4384113143757819756408409 3288084857818364817306307)
                ·
                  refine ⟨4932127286727547225959461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3288084857818364817306307 4932127286727547225959461)
                  ·
                    refine ⟨924773866261415104867399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4932127286727547225959461 924773866261415104867399)
                    ·
                      rfl

theorem cell22_2701486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_2701486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701486 prefixEnd_2701486 := by exact prefixLift 2701486
  have htrace : WordTrace (prefixWord ++ tailWord_2701486) baseStart_2701486 baseEnd_2701486 := by
    simpa [prefixWord, tailWord_2701486, baseEnd_2701486] using wordTrace_append hprefix tailTrace_2701486
  have hstable : (prefixWord ++ tailWord_2701486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701486).length < 2 ^ (prefixWord ++ tailWord_2701486).sum := by decide
  have hdescent : baseEnd_2701486 < baseStart_2701486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
