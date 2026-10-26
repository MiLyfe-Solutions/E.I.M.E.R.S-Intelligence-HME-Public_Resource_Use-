import V185TrunkScan22Chunk093

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_842940 : List Nat := [2, 2, 2, 3, 2, 2, 3, 6]
def baseStart_842940 : Nat := 118140960795 + 842940 * 2 ^ 59
def prefixEnd_842940 : Nat := 4983230072969 + 3 ^ 40 * 842940 * 2
def baseEnd_842940 : Nat := 32061732066743498301733

theorem tailTrace_842940 : CollatzResearch.WordTrace tailWord_842940 prefixEnd_842940 32061732066743498301733 := by
  unfold tailWord_842940
  simp only [CollatzResearch.WordTrace]
  refine ⟨15372273783089908767827137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20496365044119878357102849 15372273783089908767827137)
  ·
    refine ⟨11529205337317431575870353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15372273783089908767827137 11529205337317431575870353)
    ·
      refine ⟨8646904002988073681902765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11529205337317431575870353 8646904002988073681902765)
      ·
        refine ⟨3242589001120527630713537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8646904002988073681902765 3242589001120527630713537)
        ·
          refine ⟨2431941750840395723035153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3242589001120527630713537 2431941750840395723035153)
          ·
            refine ⟨1823956313130296792276365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2431941750840395723035153 1823956313130296792276365)
            ·
              refine ⟨683983617423861297103637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1823956313130296792276365 683983617423861297103637)
              ·
                refine ⟨32061732066743498301733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 683983617423861297103637 32061732066743498301733)
                ·
                  rfl

theorem cell22_842940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 6].length) (baseStart_842940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842940 prefixEnd_842940 := by exact prefixLift 842940
  have htrace : WordTrace (prefixWord ++ tailWord_842940) baseStart_842940 baseEnd_842940 := by
    simpa [prefixWord, tailWord_842940, baseEnd_842940] using wordTrace_append hprefix tailTrace_842940
  have hstable : (prefixWord ++ tailWord_842940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842940).length < 2 ^ (prefixWord ++ tailWord_842940).sum := by decide
  have hdescent : baseEnd_842940 < baseStart_842940 := by decide
  rcases family_descends (prefixWord ++ tailWord_842940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842942 : List Nat := [4, 2, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_842942 : Nat := 118140960795 + 842942 * 2 ^ 59
def prefixEnd_842942 : Nat := 4983230072969 + 3 ^ 40 * 842942 * 2
def baseEnd_842942 : Nat := 288556273241564146165591

theorem tailTrace_842942 : CollatzResearch.WordTrace tailWord_842942 prefixEnd_842942 288556273241564146165591 := by
  unfold tailWord_842942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3843077564021571484653385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20496413674781714584818053 3843077564021571484653385)
  ·
    refine ⟨2882308173016178613490039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3843077564021571484653385 2882308173016178613490039)
    ·
      refine ⟨4323462259524267920235059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2882308173016178613490039 4323462259524267920235059)
      ·
        refine ⟨6485193389286401880352589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4323462259524267920235059 6485193389286401880352589)
        ·
          refine ⟨2431947520982400705132221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6485193389286401880352589 2431947520982400705132221)
          ·
            refine ⟨911980320368400264424583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2431947520982400705132221 911980320368400264424583)
            ·
              refine ⟨1367970480552600396636875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911980320368400264424583 1367970480552600396636875)
              ·
                refine ⟨2051955720828900594955313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1367970480552600396636875 2051955720828900594955313)
                ·
                  refine ⟨1538966790621675446216485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2051955720828900594955313 1538966790621675446216485)
                  ·
                    refine ⟨288556273241564146165591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1538966790621675446216485 288556273241564146165591)
                    ·
                      rfl

theorem cell22_842942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_842942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842942 prefixEnd_842942 := by exact prefixLift 842942
  have htrace : WordTrace (prefixWord ++ tailWord_842942) baseStart_842942 baseEnd_842942 := by
    simpa [prefixWord, tailWord_842942, baseEnd_842942] using wordTrace_append hprefix tailTrace_842942
  have hstable : (prefixWord ++ tailWord_842942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842942).length < 2 ^ (prefixWord ++ tailWord_842942).sum := by decide
  have hdescent : baseEnd_842942 < baseStart_842942 := by decide
  rcases family_descends (prefixWord ++ tailWord_842942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842946 : List Nat := [3, 5, 1, 1, 2, 1, 2, 3, 4]
def baseStart_842946 : Nat := 118140960795 + 842946 * 2 ^ 59
def prefixEnd_842946 : Nat := 4983230072969 + 3 ^ 40 * 842946 * 2
def baseEnd_842946 : Nat := 96185880841103156355193

theorem tailTrace_842946 : CollatzResearch.WordTrace tailWord_842946 prefixEnd_842946 96185880841103156355193 := by
  unfold tailWord_842946
  simp only [CollatzResearch.WordTrace]
  refine ⟨7686191601039520140093173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20496510936105387040248461 7686191601039520140093173)
  ·
    refine ⟨720580462597455013133735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7686191601039520140093173 720580462597455013133735)
    ·
      refine ⟨1080870693896182519700603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 720580462597455013133735 1080870693896182519700603)
      ·
        refine ⟨1621306040844273779550905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1080870693896182519700603 1621306040844273779550905)
        ·
          refine ⟨1215979530633205334663179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1621306040844273779550905 1215979530633205334663179)
          ·
            refine ⟨1823969295949808001994769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215979530633205334663179 1823969295949808001994769)
            ·
              refine ⟨1367976971962356001496077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1823969295949808001994769 1367976971962356001496077)
              ·
                refine ⟨512991364485883500561029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1367976971962356001496077 512991364485883500561029)
                ·
                  refine ⟨96185880841103156355193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 512991364485883500561029 96185880841103156355193)
                  ·
                    rfl

theorem cell22_842946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_842946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842946 prefixEnd_842946 := by exact prefixLift 842946
  have htrace : WordTrace (prefixWord ++ tailWord_842946) baseStart_842946 baseEnd_842946 := by
    simpa [prefixWord, tailWord_842946, baseEnd_842946] using wordTrace_append hprefix tailTrace_842946
  have hstable : (prefixWord ++ tailWord_842946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842946).length < 2 ^ (prefixWord ++ tailWord_842946).sum := by decide
  have hdescent : baseEnd_842946 < baseStart_842946 := by decide
  rcases family_descends (prefixWord ++ tailWord_842946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842957 : List Nat := [1, 6, 2, 2, 1, 1, 9]
def baseStart_842957 : Nat := 118140960795 + 842957 * 2 ^ 59
def prefixEnd_842957 : Nat := 4983230072969 + 3 ^ 40 * 842957 * 2
def baseEnd_842957 : Nat := 10687459557337374334835

theorem tailTrace_842957 : CollatzResearch.WordTrace tailWord_842957 prefixEnd_842957 10687459557337374334835 := by
  unfold tailWord_842957
  simp only [CollatzResearch.WordTrace]
  refine ⟨30745167607118229439023125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20496778404745486292682083 30745167607118229439023125)
  ·
    refine ⟨1441179731583667004954209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30745167607118229439023125 1441179731583667004954209)
    ·
      refine ⟨1080884798687750253715657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1441179731583667004954209 1080884798687750253715657)
      ·
        refine ⟨810663599015812690286743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1080884798687750253715657 810663599015812690286743)
        ·
          refine ⟨1215995398523719035430115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810663599015812690286743 1215995398523719035430115)
          ·
            refine ⟨1823993097785578553145173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215995398523719035430115 1823993097785578553145173)
            ·
              refine ⟨10687459557337374334835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1823993097785578553145173 10687459557337374334835)
              ·
                rfl

theorem cell22_842957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 9].length) (baseStart_842957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842957 prefixEnd_842957 := by exact prefixLift 842957
  have htrace : WordTrace (prefixWord ++ tailWord_842957) baseStart_842957 baseEnd_842957 := by
    simpa [prefixWord, tailWord_842957, baseEnd_842957] using wordTrace_append hprefix tailTrace_842957
  have hstable : (prefixWord ++ tailWord_842957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842957).length < 2 ^ (prefixWord ++ tailWord_842957).sum := by decide
  have hdescent : baseEnd_842957 < baseStart_842957 := by decide
  rcases family_descends (prefixWord ++ tailWord_842957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843006 : List Nat := [4, 2, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_843006 : Nat := 118140960795 + 843006 * 2 ^ 59
def prefixEnd_843006 : Nat := 4983230072969 + 3 ^ 40 * 843006 * 2
def baseEnd_843006 : Nat := 288578181749489312565395

theorem tailTrace_843006 : CollatzResearch.WordTrace tailWord_843006 prefixEnd_843006 288578181749489312565395 := by
  unfold tailWord_843006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3843369347992588850944609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20497969855960473871704581 3843369347992588850944609)
  ·
    refine ⟨2882527010994441638208457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3843369347992588850944609 2882527010994441638208457)
    ·
      refine ⟨2161895258245831228656343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2882527010994441638208457 2161895258245831228656343)
      ·
        refine ⟨3242842887368746842984515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2161895258245831228656343 3242842887368746842984515)
        ·
          refine ⟨4864264331053120264476773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3242842887368746842984515 4864264331053120264476773)
          ·
            refine ⟨912049562072460049589395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4864264331053120264476773 912049562072460049589395)
            ·
              refine ⟨1368074343108690074384093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 912049562072460049589395 1368074343108690074384093)
              ·
                refine ⟨513027878665758777894035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1368074343108690074384093 513027878665758777894035)
                ·
                  refine ⟨769541817998638166841053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513027878665758777894035 769541817998638166841053)
                  ·
                    refine ⟨288578181749489312565395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 769541817998638166841053 288578181749489312565395)
                    ·
                      rfl

theorem cell22_843006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_843006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843006 prefixEnd_843006 := by exact prefixLift 843006
  have htrace : WordTrace (prefixWord ++ tailWord_843006) baseStart_843006 baseEnd_843006 := by
    simpa [prefixWord, tailWord_843006, baseEnd_843006] using wordTrace_append hprefix tailTrace_843006
  have hstable : (prefixWord ++ tailWord_843006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843006).length < 2 ^ (prefixWord ++ tailWord_843006).sum := by decide
  have hdescent : baseEnd_843006 < baseStart_843006 := by decide
  rcases family_descends (prefixWord ++ tailWord_843006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843088 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 1, 8]
def baseStart_843088 : Nat := 118140960795 + 843088 * 2 ^ 59
def prefixEnd_843088 : Nat := 4983230072969 + 3 ^ 40 * 843088 * 2
def baseEnd_843088 : Nat := 288606252025268432015143

theorem tailTrace_843088 : CollatzResearch.WordTrace tailWord_843088 prefixEnd_843088 288606252025268432015143 := by
  unfold tailWord_843088
  simp only [CollatzResearch.WordTrace]
  refine ⟨15374972784821819406020959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20499963713095759208027945 15374972784821819406020959)
  ·
    refine ⟨23062459177232729109031439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15374972784821819406020959 23062459177232729109031439)
    ·
      refine ⟨34593688765849093663547159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23062459177232729109031439 34593688765849093663547159)
      ·
        refine ⟨51890533148773640495320739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34593688765849093663547159 51890533148773640495320739)
        ·
          refine ⟨77835799723160460742981109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51890533148773640495320739 77835799723160460742981109)
          ·
            refine ⟨7297106224046293194654479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77835799723160460742981109 7297106224046293194654479)
            ·
              refine ⟨10945659336069439791981719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7297106224046293194654479 10945659336069439791981719)
              ·
                refine ⟨16418489004104159687972579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10945659336069439791981719 16418489004104159687972579)
                ·
                  refine ⟨24627733506156239531958869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16418489004104159687972579 24627733506156239531958869)
                  ·
                    refine ⟨288606252025268432015143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24627733506156239531958869 288606252025268432015143)
                    ·
                      rfl

theorem cell22_843088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_843088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843088 prefixEnd_843088 := by exact prefixLift 843088
  have htrace : WordTrace (prefixWord ++ tailWord_843088) baseStart_843088 baseEnd_843088 := by
    simpa [prefixWord, tailWord_843088, baseEnd_843088] using wordTrace_append hprefix tailTrace_843088
  have hstable : (prefixWord ++ tailWord_843088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843088).length < 2 ^ (prefixWord ++ tailWord_843088).sum := by decide
  have hdescent : baseEnd_843088 < baseStart_843088 := by decide
  rcases family_descends (prefixWord ++ tailWord_843088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843103 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 9]
def baseStart_843103 : Nat := 118140960795 + 843103 * 2 ^ 59
def prefixEnd_843103 : Nat := 4983230072969 + 3 ^ 40 * 843103 * 2
def baseEnd_843103 : Nat := 96203795610604464296699

theorem tailTrace_843103 : CollatzResearch.WordTrace tailWord_843103 prefixEnd_843103 96203795610604464296699 := by
  unfold tailWord_843103
  simp only [CollatzResearch.WordTrace]
  refine ⟨30750492664589296373837963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20500328443059530915891975 30750492664589296373837963)
  ·
    refine ⟨46125738996883944560756945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30750492664589296373837963 46125738996883944560756945)
    ·
      refine ⟨34594304247662958420567709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46125738996883944560756945 34594304247662958420567709)
      ·
        refine ⟨12972864092873609407712891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34594304247662958420567709 12972864092873609407712891)
        ·
          refine ⟨19459296139310414111569337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12972864092873609407712891 19459296139310414111569337)
          ·
            refine ⟨14594472104482810583677003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19459296139310414111569337 14594472104482810583677003)
            ·
              refine ⟨21891708156724215875515505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14594472104482810583677003 21891708156724215875515505)
              ·
                refine ⟨16418781117543161906636629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21891708156724215875515505 16418781117543161906636629)
                ·
                  refine ⟨96203795610604464296699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16418781117543161906636629 96203795610604464296699)
                  ·
                    rfl

theorem cell22_843103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 9].length) (baseStart_843103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843103 prefixEnd_843103 := by exact prefixLift 843103
  have htrace : WordTrace (prefixWord ++ tailWord_843103) baseStart_843103 baseEnd_843103 := by
    simpa [prefixWord, tailWord_843103, baseEnd_843103] using wordTrace_append hprefix tailTrace_843103
  have hstable : (prefixWord ++ tailWord_843103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843103).length < 2 ^ (prefixWord ++ tailWord_843103).sum := by decide
  have hdescent : baseEnd_843103 < baseStart_843103 := by decide
  rcases family_descends (prefixWord ++ tailWord_843103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843107 : List Nat := [1, 1, 1, 5, 2, 3, 1, 2, 3, 3]
def baseStart_843107 : Nat := 118140960795 + 843107 * 2 ^ 59
def prefixEnd_843107 : Nat := 4983230072969 + 3 ^ 40 * 843107 * 2
def baseEnd_843107 : Nat := 288612756113558715790085

theorem tailTrace_843107 : CollatzResearch.WordTrace tailWord_843107 prefixEnd_843107 288612756113558715790085 := by
  unfold tailWord_843107
  simp only [CollatzResearch.WordTrace]
  refine ⟨30750638556574805056983575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20500425704383203371322383 30750638556574805056983575)
  ·
    refine ⟨46125957834862207585475363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30750638556574805056983575 46125957834862207585475363)
    ·
      refine ⟨69188936752293311378213045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46125957834862207585475363 69188936752293311378213045)
      ·
        refine ⟨6486462820527497941707473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69188936752293311378213045 6486462820527497941707473)
        ·
          refine ⟨4864847115395623456280605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6486462820527497941707473 4864847115395623456280605)
          ·
            refine ⟨1824317668273358796105227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4864847115395623456280605 1824317668273358796105227)
            ·
              refine ⟨2736476502410038194157841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1824317668273358796105227 2736476502410038194157841)
              ·
                refine ⟨2052357376807528645618381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2736476502410038194157841 2052357376807528645618381)
                ·
                  refine ⟨769634016302823242106893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2052357376807528645618381 769634016302823242106893)
                  ·
                    refine ⟨288612756113558715790085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 769634016302823242106893 288612756113558715790085)
                    ·
                      rfl

theorem cell22_843107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 3].length) (baseStart_843107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843107 prefixEnd_843107 := by exact prefixLift 843107
  have htrace : WordTrace (prefixWord ++ tailWord_843107) baseStart_843107 baseEnd_843107 := by
    simpa [prefixWord, tailWord_843107, baseEnd_843107] using wordTrace_append hprefix tailTrace_843107
  have hstable : (prefixWord ++ tailWord_843107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843107).length < 2 ^ (prefixWord ++ tailWord_843107).sum := by decide
  have hdescent : baseEnd_843107 < baseStart_843107 := by decide
  rcases family_descends (prefixWord ++ tailWord_843107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843137 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 7]
def baseStart_843137 : Nat := 118140960795 + 843137 * 2 ^ 59
def prefixEnd_843137 : Nat := 4983230072969 + 3 ^ 40 * 843137 * 2
def baseEnd_843137 : Nat := 96207675242216212513331

theorem tailTrace_843137 : CollatzResearch.WordTrace tailWord_843137 prefixEnd_843137 96207675242216212513331 := by
  unfold tailWord_843137
  simp only [CollatzResearch.WordTrace]
  refine ⟨30751732746466120180575665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20501155164310746787050443 30751732746466120180575665)
  ·
    refine ⟨23063799559849590135431749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30751732746466120180575665 23063799559849590135431749)
    ·
      refine ⟨4324462417471798150393453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23063799559849590135431749 4324462417471798150393453)
      ·
        refine ⟨1621673406551924306397545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4324462417471798150393453 1621673406551924306397545)
        ·
          refine ⟨1216255054913943229798159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1621673406551924306397545 1216255054913943229798159)
          ·
            refine ⟨1824382582370914844697239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216255054913943229798159 1824382582370914844697239)
            ·
              refine ⟨2736573873556372267045859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1824382582370914844697239 2736573873556372267045859)
              ·
                refine ⟨4104860810334558400568789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2736573873556372267045859 4104860810334558400568789)
                ·
                  refine ⟨96207675242216212513331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4104860810334558400568789 96207675242216212513331)
                  ·
                    rfl

theorem cell22_843137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 7].length) (baseStart_843137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843137 prefixEnd_843137 := by exact prefixLift 843137
  have htrace : WordTrace (prefixWord ++ tailWord_843137) baseStart_843137 baseEnd_843137 := by
    simpa [prefixWord, tailWord_843137, baseEnd_843137] using wordTrace_append hprefix tailTrace_843137
  have hstable : (prefixWord ++ tailWord_843137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843137).length < 2 ^ (prefixWord ++ tailWord_843137).sum := by decide
  have hdescent : baseEnd_843137 < baseStart_843137 := by decide
  rcases family_descends (prefixWord ++ tailWord_843137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843167 : List Nat := [1, 1, 2, 5, 1, 2, 1, 4, 1, 4]
def baseStart_843167 : Nat := 118140960795 + 843167 * 2 ^ 59
def prefixEnd_843167 : Nat := 4983230072969 + 3 ^ 40 * 843167 * 2
def baseEnd_843167 : Nat := 288633295339738559289901

theorem tailTrace_843167 : CollatzResearch.WordTrace tailWord_843167 prefixEnd_843167 288633295339738559289901 := by
  unfold tailWord_843167
  simp only [CollatzResearch.WordTrace]
  refine ⟨30752826936357435304167755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20501884624238290202778503 30752826936357435304167755)
  ·
    refine ⟨46129240404536152956251633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30752826936357435304167755 46129240404536152956251633)
    ·
      refine ⟨34596930303402114717188725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46129240404536152956251633 34596930303402114717188725)
      ·
        refine ⟨3243462215943948254736443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34596930303402114717188725 3243462215943948254736443)
        ·
          refine ⟨4865193323915922382104665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3243462215943948254736443 4865193323915922382104665)
          ·
            refine ⟨3648894992936941786578499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4865193323915922382104665 3648894992936941786578499)
            ·
              refine ⟨5473342489405412679867749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3648894992936941786578499 5473342489405412679867749)
              ·
                refine ⟨1026251716763514877475203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5473342489405412679867749 1026251716763514877475203)
                ·
                  refine ⟨1539377575145272316212805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1026251716763514877475203 1539377575145272316212805)
                  ·
                    refine ⟨288633295339738559289901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1539377575145272316212805 288633295339738559289901)
                    ·
                      rfl

theorem cell22_843167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 4].length) (baseStart_843167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843167 prefixEnd_843167 := by exact prefixLift 843167
  have htrace : WordTrace (prefixWord ++ tailWord_843167) baseStart_843167 baseEnd_843167 := by
    simpa [prefixWord, tailWord_843167, baseEnd_843167] using wordTrace_append hprefix tailTrace_843167
  have hstable : (prefixWord ++ tailWord_843167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843167).length < 2 ^ (prefixWord ++ tailWord_843167).sum := by decide
  have hdescent : baseEnd_843167 < baseStart_843167 := by decide
  rcases family_descends (prefixWord ++ tailWord_843167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843180 : List Nat := [2, 2, 1, 1, 1, 1, 4, 4, 1, 5]
def baseStart_843180 : Nat := 118140960795 + 843180 * 2 ^ 59
def prefixEnd_843180 : Nat := 4983230072969 + 3 ^ 40 * 843180 * 2
def baseEnd_843180 : Nat := 288637745505410858714861

theorem tailTrace_843180 : CollatzResearch.WordTrace tailWord_843180 prefixEnd_843180 288637745505410858714861 := by
  unfold tailWord_843180
  simp only [CollatzResearch.WordTrace]
  refine ⟨15376650542655169262195497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20502200723540225682927329 15376650542655169262195497)
  ·
    refine ⟨11532487906991376946646623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15376650542655169262195497 11532487906991376946646623)
    ·
      refine ⟨17298731860487065419969935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11532487906991376946646623 17298731860487065419969935)
      ·
        refine ⟨25948097790730598129954903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17298731860487065419969935 25948097790730598129954903)
        ·
          refine ⟨38922146686095897194932355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25948097790730598129954903 38922146686095897194932355)
          ·
            refine ⟨58383220029143845792398533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38922146686095897194932355 58383220029143845792398533)
            ·
              refine ⟨10946853755464471086074725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58383220029143845792398533 10946853755464471086074725)
              ·
                refine ⟨2052535079149588328639011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10946853755464471086074725 2052535079149588328639011)
                ·
                  refine ⟨3078802618724382492958517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2052535079149588328639011 3078802618724382492958517)
                  ·
                    refine ⟨288637745505410858714861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3078802618724382492958517 288637745505410858714861)
                    ·
                      rfl

theorem cell22_843180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_843180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843180 prefixEnd_843180 := by exact prefixLift 843180
  have htrace : WordTrace (prefixWord ++ tailWord_843180) baseStart_843180 baseEnd_843180 := by
    simpa [prefixWord, tailWord_843180, baseEnd_843180] using wordTrace_append hprefix tailTrace_843180
  have hstable : (prefixWord ++ tailWord_843180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843180).length < 2 ^ (prefixWord ++ tailWord_843180).sum := by decide
  have hdescent : baseEnd_843180 < baseStart_843180 := by decide
  rcases family_descends (prefixWord ++ tailWord_843180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843197 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 4, 3]
def baseStart_843197 : Nat := 118140960795 + 843197 * 2 ^ 59
def prefixEnd_843197 : Nat := 4983230072969 + 3 ^ 40 * 843197 * 2
def baseEnd_843197 : Nat := 288643564952828481039809

theorem tailTrace_843197 : CollatzResearch.WordTrace tailWord_843197 prefixEnd_843197 288643564952828481039809 := by
  unfold tailWord_843197
  simp only [CollatzResearch.WordTrace]
  refine ⟨30753921126248750427759845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20502614084165833618506563 30753921126248750427759845)
  ·
    refine ⟨5766360211171640705204971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30753921126248750427759845 5766360211171640705204971)
    ·
      refine ⟨8649540316757461057807457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5766360211171640705204971 8649540316757461057807457)
      ·
        refine ⟨6487155237568095793355593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8649540316757461057807457 6487155237568095793355593)
        ·
          refine ⟨4865366428176071845016695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6487155237568095793355593 4865366428176071845016695)
          ·
            refine ⟨7298049642264107767525043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4865366428176071845016695 7298049642264107767525043)
            ·
              refine ⟨10947074463396161651287565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7298049642264107767525043 10947074463396161651287565)
              ·
                refine ⟨4105152923773560619232837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10947074463396161651287565 4105152923773560619232837)
                ·
                  refine ⟨769716173207542616106157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4105152923773560619232837 769716173207542616106157)
                  ·
                    refine ⟨288643564952828481039809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 769716173207542616106157 288643564952828481039809)
                    ·
                      rfl

theorem cell22_843197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_843197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843197 prefixEnd_843197 := by exact prefixLift 843197
  have htrace : WordTrace (prefixWord ++ tailWord_843197) baseStart_843197 baseEnd_843197 := by
    simpa [prefixWord, tailWord_843197, baseEnd_843197] using wordTrace_append hprefix tailTrace_843197
  have hstable : (prefixWord ++ tailWord_843197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843197).length < 2 ^ (prefixWord ++ tailWord_843197).sum := by decide
  have hdescent : baseEnd_843197 < baseStart_843197 := by decide
  rcases family_descends (prefixWord ++ tailWord_843197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843210 : List Nat := [3, 1, 2, 1, 2, 3, 1, 9]
def baseStart_843210 : Nat := 118140960795 + 843210 * 2 ^ 59
def prefixEnd_843210 : Nat := 4983230072969 + 3 ^ 40 * 843210 * 2
def baseEnd_843210 : Nat := 32072001679833420051641

theorem tailTrace_843210 : CollatzResearch.WordTrace tailWord_843210 prefixEnd_843210 32072001679833420051641 := by
  unfold tailWord_843210
  simp only [CollatzResearch.WordTrace]
  refine ⟨7688598818800413411995771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20502930183467769098655389 7688598818800413411995771)
  ·
    refine ⟨11532898228200620117993657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7688598818800413411995771 11532898228200620117993657)
    ·
      refine ⟨8649673671150465088495243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11532898228200620117993657 8649673671150465088495243)
      ·
        refine ⟨12974510506725697632742865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8649673671150465088495243 12974510506725697632742865)
        ·
          refine ⟨9730882880044273224557149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12974510506725697632742865 9730882880044273224557149)
          ·
            refine ⟨3649081080016602459208931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9730882880044273224557149 3649081080016602459208931)
            ·
              refine ⟨5473621620024903688813397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3649081080016602459208931 5473621620024903688813397)
              ·
                refine ⟨32072001679833420051641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5473621620024903688813397 32072001679833420051641)
                ·
                  rfl

theorem cell22_843210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 9].length) (baseStart_843210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843210 prefixEnd_843210 := by exact prefixLift 843210
  have htrace : WordTrace (prefixWord ++ tailWord_843210) baseStart_843210 baseEnd_843210 := by
    simpa [prefixWord, tailWord_843210, baseEnd_843210] using wordTrace_append hprefix tailTrace_843210
  have hstable : (prefixWord ++ tailWord_843210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843210).length < 2 ^ (prefixWord ++ tailWord_843210).sum := by decide
  have hdescent : baseEnd_843210 < baseStart_843210 := by decide
  rcases family_descends (prefixWord ++ tailWord_843210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843229 : List Nat := [1, 4, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_843229 : Nat := 118140960795 + 843229 * 2 ^ 59
def prefixEnd_843229 : Nat := 4983230072969 + 3 ^ 40 * 843229 * 2
def baseEnd_843229 : Nat := 288654519206791064239711

theorem tailTrace_843229 : CollatzResearch.WordTrace tailWord_843229 prefixEnd_843229 288654519206791064239711 := by
  unfold tailWord_843229
  simp only [CollatzResearch.WordTrace]
  refine ⟨30755088262132819892924741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20503392174755213261949827 30755088262132819892924741)
  ·
    refine ⟨5766579049149903729923389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30755088262132819892924741 5766579049149903729923389)
    ·
      refine ⟨2162467143431213898721271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5766579049149903729923389 2162467143431213898721271)
      ·
        refine ⟨3243700715146820848081907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2162467143431213898721271 3243700715146820848081907)
        ·
          refine ⟨4865551072720231272122861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3243700715146820848081907 4865551072720231272122861)
          ·
            refine ⟨1824581652270086727046073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4865551072720231272122861 1824581652270086727046073)
            ·
              refine ⟨1368436239202565045284555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1824581652270086727046073 1368436239202565045284555)
              ·
                refine ⟨2052654358803847567926833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368436239202565045284555 2052654358803847567926833)
                ·
                  refine ⟨1539490769102885675945125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2052654358803847567926833 1539490769102885675945125)
                  ·
                    refine ⟨288654519206791064239711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1539490769102885675945125 288654519206791064239711)
                    ·
                      rfl

theorem cell22_843229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_843229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843229 prefixEnd_843229 := by exact prefixLift 843229
  have htrace : WordTrace (prefixWord ++ tailWord_843229) baseStart_843229 baseEnd_843229 := by
    simpa [prefixWord, tailWord_843229, baseEnd_843229] using wordTrace_append hprefix tailTrace_843229
  have hstable : (prefixWord ++ tailWord_843229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843229).length < 2 ^ (prefixWord ++ tailWord_843229).sum := by decide
  have hdescent : baseEnd_843229 < baseStart_843229 := by decide
  rcases family_descends (prefixWord ++ tailWord_843229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843259 : List Nat := [1, 1, 1, 1, 1, 3, 2, 8, 1, 3]
def baseStart_843259 : Nat := 118140960795 + 843259 * 2 ^ 59
def prefixEnd_843259 : Nat := 4983230072969 + 3 ^ 40 * 843259 * 2
def baseEnd_843259 : Nat := 288664788819880985989619

theorem tailTrace_843259 : CollatzResearch.WordTrace tailWord_843259 prefixEnd_843259 288664788819880985989619 := by
  unfold tailWord_843259
  simp only [CollatzResearch.WordTrace]
  refine ⟨30756182452024135016516831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20504121634682756677677887 30756182452024135016516831)
  ·
    refine ⟨46134273678036202524775247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30756182452024135016516831 46134273678036202524775247)
    ·
      refine ⟨69201410517054303787162871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46134273678036202524775247 69201410517054303787162871)
      ·
        refine ⟨103802115775581455680744307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69201410517054303787162871 103802115775581455680744307)
        ·
          refine ⟨155703173663372183521116461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103802115775581455680744307 155703173663372183521116461)
          ·
            refine ⟨58388690123764568820418673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155703173663372183521116461 58388690123764568820418673)
            ·
              refine ⟨43791517592823426615314005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58388690123764568820418673 43791517592823426615314005)
              ·
                refine ⟨513181846790899530648211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 43791517592823426615314005 513181846790899530648211)
                ·
                  refine ⟨769772770186349295972317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513181846790899530648211 769772770186349295972317)
                  ·
                    refine ⟨288664788819880985989619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 769772770186349295972317 288664788819880985989619)
                    ·
                      rfl

theorem cell22_843259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 1, 3].length) (baseStart_843259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843259 prefixEnd_843259 := by exact prefixLift 843259
  have htrace : WordTrace (prefixWord ++ tailWord_843259) baseStart_843259 baseEnd_843259 := by
    simpa [prefixWord, tailWord_843259, baseEnd_843259] using wordTrace_append hprefix tailTrace_843259
  have hstable : (prefixWord ++ tailWord_843259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843259).length < 2 ^ (prefixWord ++ tailWord_843259).sum := by decide
  have hdescent : baseEnd_843259 < baseStart_843259 := by decide
  rcases family_descends (prefixWord ++ tailWord_843259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843272 : List Nat := [2, 1, 3, 2, 1, 1, 4, 3, 5]
def baseStart_843272 : Nat := 118140960795 + 843272 * 2 ^ 59
def prefixEnd_843272 : Nat := 4983230072969 + 3 ^ 40 * 843272 * 2
def baseEnd_843272 : Nat := 96223079661851095138193

theorem tailTrace_843272 : CollatzResearch.WordTrace tailWord_843272 prefixEnd_843272 96223079661851095138193 := by
  unfold tailWord_843272
  simp only [CollatzResearch.WordTrace]
  refine ⟨15378328300488519118370035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20504437733984692157826713 15378328300488519118370035)
  ·
    refine ⟨23067492450732778677555053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15378328300488519118370035 23067492450732778677555053)
    ·
      refine ⟨8650309669024792004083145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23067492450732778677555053 8650309669024792004083145)
      ·
        refine ⟨6487732251768594003062359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8650309669024792004083145 6487732251768594003062359)
        ·
          refine ⟨9731598377652891004593539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6487732251768594003062359 9731598377652891004593539)
          ·
            refine ⟨14597397566479336506890309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9731598377652891004593539 14597397566479336506890309)
            ·
              refine ⟨2737012043714875595041933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14597397566479336506890309 2737012043714875595041933)
              ·
                refine ⟨1026379516393078348140725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2737012043714875595041933 1026379516393078348140725)
                ·
                  refine ⟨96223079661851095138193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1026379516393078348140725 96223079661851095138193)
                  ·
                    rfl

theorem cell22_843272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 5].length) (baseStart_843272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843272 prefixEnd_843272 := by exact prefixLift 843272
  have htrace : WordTrace (prefixWord ++ tailWord_843272) baseStart_843272 baseEnd_843272 := by
    simpa [prefixWord, tailWord_843272, baseEnd_843272] using wordTrace_append hprefix tailTrace_843272
  have hstable : (prefixWord ++ tailWord_843272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843272).length < 2 ^ (prefixWord ++ tailWord_843272).sum := by decide
  have hdescent : baseEnd_843272 < baseStart_843272 := by decide
  rcases family_descends (prefixWord ++ tailWord_843272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843317 : List Nat := [1, 3, 3, 1, 1, 3, 1, 3, 6]
def baseStart_843317 : Nat := 118140960795 + 843317 * 2 ^ 59
def prefixEnd_843317 : Nat := 4983230072969 + 3 ^ 40 * 843317 * 2
def baseEnd_843317 : Nat := 96228214468396056013147

theorem tailTrace_843317 : CollatzResearch.WordTrace tailWord_843317 prefixEnd_843317 96228214468396056013147 := by
  unfold tailWord_843317
  simp only [CollatzResearch.WordTrace]
  refine ⟨30758297885814010922128205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20505531923876007281418803 30758297885814010922128205)
  ·
    refine ⟨11534361707180254095798077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30758297885814010922128205 11534361707180254095798077)
    ·
      refine ⟨4325385640192595285924279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11534361707180254095798077 4325385640192595285924279)
      ·
        refine ⟨6488078460288892928886419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4325385640192595285924279 6488078460288892928886419)
        ·
          refine ⟨9732117690433339393329629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6488078460288892928886419 9732117690433339393329629)
          ·
            refine ⟨3649544133912502272498611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9732117690433339393329629 3649544133912502272498611)
            ·
              refine ⟨5474316200868753408747917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3649544133912502272498611 5474316200868753408747917)
              ·
                refine ⟨2052868575325782528280469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5474316200868753408747917 2052868575325782528280469)
                ·
                  refine ⟨96228214468396056013147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2052868575325782528280469 96228214468396056013147)
                  ·
                    rfl

theorem cell22_843317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_843317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843317 prefixEnd_843317 := by exact prefixLift 843317
  have htrace : WordTrace (prefixWord ++ tailWord_843317) baseStart_843317 baseEnd_843317 := by
    simpa [prefixWord, tailWord_843317, baseEnd_843317] using wordTrace_append hprefix tailTrace_843317
  have hstable : (prefixWord ++ tailWord_843317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843317).length < 2 ^ (prefixWord ++ tailWord_843317).sum := by decide
  have hdescent : baseEnd_843317 < baseStart_843317 := by decide
  rcases family_descends (prefixWord ++ tailWord_843317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843351 : List Nat := [1, 1, 3, 2, 2, 5, 1, 3, 4]
def baseStart_843351 : Nat := 118140960795 + 843351 * 2 ^ 59
def prefixEnd_843351 : Nat := 4983230072969 + 3 ^ 40 * 843351 * 2
def baseEnd_843351 : Nat := 96232094100007804229779

theorem tailTrace_843351 : CollatzResearch.WordTrace tailWord_843351 prefixEnd_843351 96232094100007804229779 := by
  unfold tailWord_843351
  simp only [CollatzResearch.WordTrace]
  refine ⟨30759537967690834728865907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20506358645127223152577271 30759537967690834728865907)
  ·
    refine ⟨46139306951536252093298861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30759537967690834728865907 46139306951536252093298861)
    ·
      refine ⟨17302240106826094534987073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46139306951536252093298861 17302240106826094534987073)
      ·
        refine ⟨12976680080119570901240305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17302240106826094534987073 12976680080119570901240305)
        ·
          refine ⟨9732510060089678175930229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12976680080119570901240305 9732510060089678175930229)
          ·
            refine ⟨912422818133407328993459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9732510060089678175930229 912422818133407328993459)
            ·
              refine ⟨1368634227200110993490189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 912422818133407328993459 1368634227200110993490189)
              ·
                refine ⟨513237835200041622558821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1368634227200110993490189 513237835200041622558821)
                ·
                  refine ⟨96232094100007804229779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 513237835200041622558821 96232094100007804229779)
                  ·
                    rfl

theorem cell22_843351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 4].length) (baseStart_843351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843351 prefixEnd_843351 := by exact prefixLift 843351
  have htrace : WordTrace (prefixWord ++ tailWord_843351) baseStart_843351 baseEnd_843351 := by
    simpa [prefixWord, tailWord_843351, baseEnd_843351] using wordTrace_append hprefix tailTrace_843351
  have hstable : (prefixWord ++ tailWord_843351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843351).length < 2 ^ (prefixWord ++ tailWord_843351).sum := by decide
  have hdescent : baseEnd_843351 < baseStart_843351 := by decide
  rcases family_descends (prefixWord ++ tailWord_843351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843364 : List Nat := [2, 3, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_843364 : Nat := 118140960795 + 843364 * 2 ^ 59
def prefixEnd_843364 : Nat := 4983230072969 + 3 ^ 40 * 843364 * 2
def baseEnd_843364 : Nat := 288700732465695712114297

theorem tailTrace_843364 : CollatzResearch.WordTrace tailWord_843364 prefixEnd_843364 288700732465695712114297 := by
  unfold tailWord_843364
  simp only [CollatzResearch.WordTrace]
  refine ⟨15380006058321868974544573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20506674744429158632726097 15380006058321868974544573)
  ·
    refine ⟨5767502271870700865454215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15380006058321868974544573 5767502271870700865454215)
    ·
      refine ⟨8651253407806051298181323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5767502271870700865454215 8651253407806051298181323)
      ·
        refine ⟨12976880111709076947271985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8651253407806051298181323 12976880111709076947271985)
        ·
          refine ⟨9732660083781807710453989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12976880111709076947271985 9732660083781807710453989)
          ·
            refine ⟨1824873765709088945710123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9732660083781807710453989 1824873765709088945710123)
            ·
              refine ⟨2737310648563633418565185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1824873765709088945710123 2737310648563633418565185)
              ·
                refine ⟨2052982986422725063923889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2737310648563633418565185 2052982986422725063923889)
                ·
                  refine ⟨1539737239817043797942917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2052982986422725063923889 1539737239817043797942917)
                  ·
                    refine ⟨288700732465695712114297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1539737239817043797942917 288700732465695712114297)
                    ·
                      rfl

theorem cell22_843364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_843364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843364 prefixEnd_843364 := by exact prefixLift 843364
  have htrace : WordTrace (prefixWord ++ tailWord_843364) baseStart_843364 baseEnd_843364 := by
    simpa [prefixWord, tailWord_843364, baseEnd_843364] using wordTrace_append hprefix tailTrace_843364
  have hstable : (prefixWord ++ tailWord_843364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843364).length < 2 ^ (prefixWord ++ tailWord_843364).sum := by decide
  have hdescent : baseEnd_843364 < baseStart_843364 := by decide
  rcases family_descends (prefixWord ++ tailWord_843364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843368 : List Nat := [2, 1, 4, 3, 1, 2, 3, 2, 4]
def baseStart_843368 : Nat := 118140960795 + 843368 * 2 ^ 59
def prefixEnd_843368 : Nat := 4983230072969 + 3 ^ 40 * 843368 * 2
def baseEnd_843368 : Nat := 96234033915813678338095

theorem tailTrace_843368 : CollatzResearch.WordTrace tailWord_843368 prefixEnd_843368 96234033915813678338095 := by
  unfold tailWord_843368
  simp only [CollatzResearch.WordTrace]
  refine ⟨15380079004314623316117379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20506772005752831088156505 15380079004314623316117379)
  ·
    refine ⟨23070118506471934974176069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15380079004314623316117379 23070118506471934974176069)
    ·
      refine ⟨4325647219963487807658013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23070118506471934974176069 4325647219963487807658013)
      ·
        refine ⟨1622117707486307927871755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4325647219963487807658013 1622117707486307927871755)
        ·
          refine ⟨2433176561229461891807633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1622117707486307927871755 2433176561229461891807633)
          ·
            refine ⟨1824882420922096418855725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2433176561229461891807633 1824882420922096418855725)
            ·
              refine ⟨684330907845786157070897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1824882420922096418855725 684330907845786157070897)
              ·
                refine ⟨513248180884339617803173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684330907845786157070897 513248180884339617803173)
                ·
                  refine ⟨96234033915813678338095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 513248180884339617803173 96234033915813678338095)
                  ·
                    rfl

theorem cell22_843368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 4].length) (baseStart_843368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843368 prefixEnd_843368 := by exact prefixLift 843368
  have htrace : WordTrace (prefixWord ++ tailWord_843368) baseStart_843368 baseEnd_843368 := by
    simpa [prefixWord, tailWord_843368, baseEnd_843368] using wordTrace_append hprefix tailTrace_843368
  have hstable : (prefixWord ++ tailWord_843368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843368).length < 2 ^ (prefixWord ++ tailWord_843368).sum := by decide
  have hdescent : baseEnd_843368 < baseStart_843368 := by decide
  rcases family_descends (prefixWord ++ tailWord_843368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843424 : List Nat := [2, 1, 1, 4, 3, 1, 1, 4, 5]
def baseStart_843424 : Nat := 118140960795 + 843424 * 2 ^ 59
def prefixEnd_843424 : Nat := 4983230072969 + 3 ^ 40 * 843424 * 2
def baseEnd_843424 : Nat := 96240423897291851871371

theorem tailTrace_843424 : CollatzResearch.WordTrace tailWord_843424 prefixEnd_843424 96240423897291851871371 := by
  unfold tailWord_843424
  simp only [CollatzResearch.WordTrace]
  refine ⟨15381100248213184098136663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20508133664284245464182217 15381100248213184098136663)
  ·
    refine ⟨23071650372319776147204995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15381100248213184098136663 23071650372319776147204995)
    ·
      refine ⟨34607475558479664220807493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23071650372319776147204995 34607475558479664220807493)
      ·
        refine ⟨6488901667214937041401405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34607475558479664220807493 6488901667214937041401405)
        ·
          refine ⟨2433338125205601390525527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6488901667214937041401405 2433338125205601390525527)
          ·
            refine ⟨3650007187808402085788291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2433338125205601390525527 3650007187808402085788291)
            ·
              refine ⟨5475010781712603128682437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3650007187808402085788291 5475010781712603128682437)
              ·
                refine ⟨1026564521571113086627957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5475010781712603128682437 1026564521571113086627957)
                ·
                  refine ⟨96240423897291851871371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1026564521571113086627957 96240423897291851871371)
                  ·
                    rfl

theorem cell22_843424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 5].length) (baseStart_843424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843424 prefixEnd_843424 := by exact prefixLift 843424
  have htrace : WordTrace (prefixWord ++ tailWord_843424) baseStart_843424 baseEnd_843424 := by
    simpa [prefixWord, tailWord_843424, baseEnd_843424] using wordTrace_append hprefix tailTrace_843424
  have hstable : (prefixWord ++ tailWord_843424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843424).length < 2 ^ (prefixWord ++ tailWord_843424).sum := by decide
  have hdescent : baseEnd_843424 < baseStart_843424 := by decide
  rcases family_descends (prefixWord ++ tailWord_843424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843428 : List Nat := [2, 3, 1, 2, 2, 3, 1, 4, 1, 3]
def baseStart_843428 : Nat := 118140960795 + 843428 * 2 ^ 59
def prefixEnd_843428 : Nat := 4983230072969 + 3 ^ 40 * 843428 * 2
def baseEnd_843428 : Nat := 288722640973620878514101

theorem tailTrace_843428 : CollatzResearch.WordTrace tailWord_843428 prefixEnd_843428 288722640973620878514101 := by
  unfold tailWord_843428
  simp only [CollatzResearch.WordTrace]
  refine ⟨15381173194205938439709469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20508230925607917919612625 15381173194205938439709469)
  ·
    refine ⟨5767939947827226914891051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15381173194205938439709469 5767939947827226914891051)
    ·
      refine ⟨8651909921740840372336577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5767939947827226914891051 8651909921740840372336577)
      ·
        refine ⟨6488932441305630279252433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8651909921740840372336577 6488932441305630279252433)
        ·
          refine ⟨4866699330979222709439325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6488932441305630279252433 4866699330979222709439325)
          ·
            refine ⟨1825012249117208516039747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4866699330979222709439325 1825012249117208516039747)
            ·
              refine ⟨2737518373675812774059621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1825012249117208516039747 2737518373675812774059621)
              ·
                refine ⟨513284695064214895136179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2737518373675812774059621 513284695064214895136179)
                ·
                  refine ⟨769927042596322342704269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513284695064214895136179 769927042596322342704269)
                  ·
                    refine ⟨288722640973620878514101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 769927042596322342704269 288722640973620878514101)
                    ·
                      rfl

theorem cell22_843428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_843428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843428 prefixEnd_843428 := by exact prefixLift 843428
  have htrace : WordTrace (prefixWord ++ tailWord_843428) baseStart_843428 baseEnd_843428 := by
    simpa [prefixWord, tailWord_843428, baseEnd_843428] using wordTrace_append hprefix tailTrace_843428
  have hstable : (prefixWord ++ tailWord_843428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843428).length < 2 ^ (prefixWord ++ tailWord_843428).sum := by decide
  have hdescent : baseEnd_843428 < baseStart_843428 := by decide
  rcases family_descends (prefixWord ++ tailWord_843428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843462 : List Nat := [6, 1, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_843462 : Nat := 118140960795 + 843462 * 2 ^ 59
def prefixEnd_843462 : Nat := 4983230072969 + 3 ^ 40 * 843462 * 2
def baseEnd_843462 : Nat := 288734279868456123163997

theorem tailTrace_843462 : CollatzResearch.WordTrace tailWord_843462 prefixEnd_843462 288734279868456123163997 := by
  unfold tailWord_843462
  simp only [CollatzResearch.WordTrace]
  refine ⟨961362077196521896442395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20509057646859133790771093 961362077196521896442395)
  ·
    refine ⟨1442043115794782844663593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 961362077196521896442395 1442043115794782844663593)
    ·
      refine ⟨1081532336846087133497695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1442043115794782844663593 1081532336846087133497695)
      ·
        refine ⟨1622298505269130700246543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1081532336846087133497695 1622298505269130700246543)
        ·
          refine ⟨2433447757903696050369815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1622298505269130700246543 2433447757903696050369815)
          ·
            refine ⟨3650171636855544075554723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2433447757903696050369815 3650171636855544075554723)
            ·
              refine ⟨5475257455283316113332085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3650171636855544075554723 5475257455283316113332085)
              ·
                refine ⟨513305386432810885624883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5475257455283316113332085 513305386432810885624883)
                ·
                  refine ⟨769958079649216328437325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513305386432810885624883 769958079649216328437325)
                  ·
                    refine ⟨288734279868456123163997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 769958079649216328437325 288734279868456123163997)
                    ·
                      rfl

theorem cell22_843462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_843462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843462 prefixEnd_843462 := by exact prefixLift 843462
  have htrace : WordTrace (prefixWord ++ tailWord_843462) baseStart_843462 baseEnd_843462 := by
    simpa [prefixWord, tailWord_843462, baseEnd_843462] using wordTrace_append hprefix tailTrace_843462
  have hstable : (prefixWord ++ tailWord_843462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843462).length < 2 ^ (prefixWord ++ tailWord_843462).sum := by decide
  have hdescent : baseEnd_843462 < baseStart_843462 := by decide
  rcases family_descends (prefixWord ++ tailWord_843462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843497 : List Nat := [1, 2, 1, 1, 1, 2, 3, 11]
def baseStart_843497 : Nat := 118140960795 + 843497 * 2 ^ 59
def prefixEnd_843497 : Nat := 4983230072969 + 3 ^ 40 * 843497 * 2
def baseEnd_843497 : Nat := 32082917898191966504321

theorem tailTrace_843497 : CollatzResearch.WordTrace tailWord_843497 prefixEnd_843497 32082917898191966504321 := by
  unfold tailWord_843497
  simp only [CollatzResearch.WordTrace]
  refine ⟨30764863025161901663680745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20509908683441267775787163 30764863025161901663680745)
  ·
    refine ⟨23073647268871426247760559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30764863025161901663680745 23073647268871426247760559)
    ·
      refine ⟨34610470903307139371640839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23073647268871426247760559 34610470903307139371640839)
      ·
        refine ⟨51915706354960709057461259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34610470903307139371640839 51915706354960709057461259)
        ·
          refine ⟨77873559532441063586191889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51915706354960709057461259 77873559532441063586191889)
          ·
            refine ⟨58405169649330797689643917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77873559532441063586191889 58405169649330797689643917)
            ·
              refine ⟨21901938618499049133616469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58405169649330797689643917 21901938618499049133616469)
              ·
                refine ⟨32082917898191966504321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 21901938618499049133616469 32082917898191966504321)
                ·
                  rfl

theorem cell22_843497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 11].length) (baseStart_843497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843497 prefixEnd_843497 := by exact prefixLift 843497
  have htrace : WordTrace (prefixWord ++ tailWord_843497) baseStart_843497 baseEnd_843497 := by
    simpa [prefixWord, tailWord_843497, baseEnd_843497] using wordTrace_append hprefix tailTrace_843497
  have hstable : (prefixWord ++ tailWord_843497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843497).length < 2 ^ (prefixWord ++ tailWord_843497).sum := by decide
  have hdescent : baseEnd_843497 < baseStart_843497 := by decide
  rcases family_descends (prefixWord ++ tailWord_843497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843501 : List Nat := [1, 5, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_843501 : Nat := 118140960795 + 843501 * 2 ^ 59
def prefixEnd_843501 : Nat := 4983230072969 + 3 ^ 40 * 843501 * 2
def baseEnd_843501 : Nat := 288747630365473021438877

theorem tailTrace_843501 : CollatzResearch.WordTrace tailWord_843501 prefixEnd_843501 288747630365473021438877 := by
  unfold tailWord_843501
  simp only [CollatzResearch.WordTrace]
  refine ⟨30765008917147410346826357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20510005944764940231217571 30765008917147410346826357)
  ·
    refine ⟨2884219585982569720014971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30765008917147410346826357 2884219585982569720014971)
    ·
      refine ⟨4326329378973854580022457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2884219585982569720014971 4326329378973854580022457)
      ·
        refine ⟨3244747034230390935016843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4326329378973854580022457 3244747034230390935016843)
        ·
          refine ⟨4867120551345586402525265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3244747034230390935016843 4867120551345586402525265)
          ·
            refine ⟨3650340413509189801893949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4867120551345586402525265 3650340413509189801893949)
            ·
              refine ⟨1368877655065946175710231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3650340413509189801893949 1368877655065946175710231)
              ·
                refine ⟨2053316482598919263565347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368877655065946175710231 2053316482598919263565347)
                ·
                  refine ⟨3079974723898378895348021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2053316482598919263565347 3079974723898378895348021)
                  ·
                    refine ⟨288747630365473021438877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3079974723898378895348021 288747630365473021438877)
                    ·
                      rfl

theorem cell22_843501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_843501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843501 prefixEnd_843501 := by exact prefixLift 843501
  have htrace : WordTrace (prefixWord ++ tailWord_843501) baseStart_843501 baseEnd_843501 := by
    simpa [prefixWord, tailWord_843501, baseEnd_843501] using wordTrace_append hprefix tailTrace_843501
  have hstable : (prefixWord ++ tailWord_843501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843501).length < 2 ^ (prefixWord ++ tailWord_843501).sum := by decide
  have hdescent : baseEnd_843501 < baseStart_843501 := by decide
  rcases family_descends (prefixWord ++ tailWord_843501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843597 : List Nat := [1, 6, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_843597 : Nat := 118140960795 + 843597 * 2 ^ 59
def prefixEnd_843597 : Nat := 4983230072969 + 3 ^ 40 * 843597 * 2
def baseEnd_843597 : Nat := 288780493127360771038583

theorem tailTrace_843597 : CollatzResearch.WordTrace tailWord_843597 prefixEnd_843597 288780493127360771038583 := by
  unfold tailWord_843597
  simp only [CollatzResearch.WordTrace]
  refine ⟨30768510324799618742321045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20512340216533079161547363 30768510324799618742321045)
  ·
    refine ⟨1442273921474982128546299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30768510324799618742321045 1442273921474982128546299)
    ·
      refine ⟨2163410882212473192819449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1442273921474982128546299 2163410882212473192819449)
      ·
        refine ⟨1622558161659354894614587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2163410882212473192819449 1622558161659354894614587)
        ·
          refine ⟨2433837242489032341921881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1622558161659354894614587 2433837242489032341921881)
          ·
            refine ⟨1825377931866774256441411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2433837242489032341921881 1825377931866774256441411)
            ·
              refine ⟨2738066897800161384662117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1825377931866774256441411 2738066897800161384662117)
              ·
                refine ⟨513387543337530259624147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2738066897800161384662117 513387543337530259624147)
                ·
                  refine ⟨770081315006295389436221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513387543337530259624147 770081315006295389436221)
                  ·
                    refine ⟨288780493127360771038583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 770081315006295389436221 288780493127360771038583)
                    ·
                      rfl

theorem cell22_843597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_843597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843597 prefixEnd_843597 := by exact prefixLift 843597
  have htrace : WordTrace (prefixWord ++ tailWord_843597) baseStart_843597 baseEnd_843597 := by
    simpa [prefixWord, tailWord_843597, baseEnd_843597] using wordTrace_append hprefix tailTrace_843597
  have hstable : (prefixWord ++ tailWord_843597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843597).length < 2 ^ (prefixWord ++ tailWord_843597).sum := by decide
  have hdescent : baseEnd_843597 < baseStart_843597 := by decide
  rcases family_descends (prefixWord ++ tailWord_843597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843664 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 2, 7]
def baseStart_843664 : Nat := 118140960795 + 843664 * 2 ^ 59
def prefixEnd_843664 : Nat := 4983230072969 + 3 ^ 40 * 843664 * 2
def baseEnd_843664 : Nat := 288803428596594929613377

theorem tailTrace_843664 : CollatzResearch.WordTrace tailWord_843664 prefixEnd_843664 288803428596594929613377 := by
  unfold tailWord_843664
  simp only [CollatzResearch.WordTrace]
  refine ⟨15385477007778444592505023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20513969343704592790006697 15385477007778444592505023)
  ·
    refine ⟨23078215511667666888757535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15385477007778444592505023 23078215511667666888757535)
    ·
      refine ⟨34617323267501500333136303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23078215511667666888757535 34617323267501500333136303)
      ·
        refine ⟨51925984901252250499704455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34617323267501500333136303 51925984901252250499704455)
        ·
          refine ⟨77888977351878375749556683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51925984901252250499704455 77888977351878375749556683)
          ·
            refine ⟨116833466027817563624335025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77888977351878375749556683 116833466027817563624335025)
            ·
              refine ⟨87625099520863172718251269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116833466027817563624335025 87625099520863172718251269)
              ·
                refine ⟨16429706160161844884672113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87625099520863172718251269 16429706160161844884672113)
                ·
                  refine ⟨12322279620121383663504085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16429706160161844884672113 12322279620121383663504085)
                  ·
                    refine ⟨288803428596594929613377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12322279620121383663504085 288803428596594929613377)
                    ·
                      rfl

theorem cell22_843664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_843664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843664 prefixEnd_843664 := by exact prefixLift 843664
  have htrace : WordTrace (prefixWord ++ tailWord_843664) baseStart_843664 baseEnd_843664 := by
    simpa [prefixWord, tailWord_843664, baseEnd_843664] using wordTrace_append hprefix tailTrace_843664
  have hstable : (prefixWord ++ tailWord_843664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843664).length < 2 ^ (prefixWord ++ tailWord_843664).sum := by decide
  have hdescent : baseEnd_843664 < baseStart_843664 := by decide
  rcases family_descends (prefixWord ++ tailWord_843664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843700 : List Nat := [2, 5, 2, 1, 2, 2, 8]
def baseStart_843700 : Nat := 118140960795 + 843700 * 2 ^ 59
def prefixEnd_843700 : Nat := 4983230072969 + 3 ^ 40 * 843700 * 2
def baseEnd_843700 : Nat := 10696879708603808730121

theorem tailTrace_843700 : CollatzResearch.WordTrace tailWord_843700 prefixEnd_843700 10696879708603808730121 := by
  unfold tailWord_843700
  simp only [CollatzResearch.WordTrace]
  refine ⟨15386133521713233666660277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20514844695617644888880369 15386133521713233666660277)
  ·
    refine ⟨1442450017660615656249401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15386133521713233666660277 1442450017660615656249401)
    ·
      refine ⟨1081837513245461742187051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1442450017660615656249401 1081837513245461742187051)
      ·
        refine ⟨1622756269868192613280577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1081837513245461742187051 1622756269868192613280577)
        ·
          refine ⟨1217067202401144459960433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1622756269868192613280577 1217067202401144459960433)
          ·
            refine ⟨912800401800858344970325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1217067202401144459960433 912800401800858344970325)
            ·
              refine ⟨10696879708603808730121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 912800401800858344970325 10696879708603808730121)
              ·
                rfl

theorem cell22_843700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 8].length) (baseStart_843700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843700 prefixEnd_843700 := by exact prefixLift 843700
  have htrace : WordTrace (prefixWord ++ tailWord_843700) baseStart_843700 baseEnd_843700 := by
    simpa [prefixWord, tailWord_843700, baseEnd_843700] using wordTrace_append hprefix tailTrace_843700
  have hstable : (prefixWord ++ tailWord_843700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843700).length < 2 ^ (prefixWord ++ tailWord_843700).sum := by decide
  have hdescent : baseEnd_843700 < baseStart_843700 := by decide
  rcases family_descends (prefixWord ++ tailWord_843700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843711 : List Nat := [1, 1, 2, 2, 2, 1, 4, 4, 5]
def baseStart_843711 : Nat := 118140960795 + 843711 * 2 ^ 59
def prefixEnd_843711 : Nat := 4983230072969 + 3 ^ 40 * 843711 * 2
def baseEnd_843711 : Nat := 96273172552367491229411

theorem tailTrace_843711 : CollatzResearch.WordTrace tailWord_843711 prefixEnd_843711 96273172552367491229411 := by
  unfold tailWord_843711
  simp only [CollatzResearch.WordTrace]
  refine ⟨30772668246386616211970987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20515112164257744141313991 30772668246386616211970987)
  ·
    refine ⟨46159002369579924317956481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30772668246386616211970987 46159002369579924317956481)
    ·
      refine ⟨34619251777184943238467361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46159002369579924317956481 34619251777184943238467361)
      ·
        refine ⟨25964438832888707428850521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34619251777184943238467361 25964438832888707428850521)
        ·
          refine ⟨19473329124666530571637891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25964438832888707428850521 19473329124666530571637891)
          ·
            refine ⟨29209993686999795857456837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19473329124666530571637891 29209993686999795857456837)
            ·
              refine ⟨5476873816312461723273157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29209993686999795857456837 5476873816312461723273157)
              ·
                refine ⟨1026913840558586573113717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5476873816312461723273157 1026913840558586573113717)
                ·
                  refine ⟨96273172552367491229411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1026913840558586573113717 96273172552367491229411)
                  ·
                    rfl

theorem cell22_843711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 5].length) (baseStart_843711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843711 prefixEnd_843711 := by exact prefixLift 843711
  have htrace : WordTrace (prefixWord ++ tailWord_843711) baseStart_843711 baseEnd_843711 := by
    simpa [prefixWord, tailWord_843711, baseEnd_843711] using wordTrace_append hprefix tailTrace_843711
  have hstable : (prefixWord ++ tailWord_843711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843711).length < 2 ^ (prefixWord ++ tailWord_843711).sum := by decide
  have hdescent : baseEnd_843711 < baseStart_843711 := by decide
  rcases family_descends (prefixWord ++ tailWord_843711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843726 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_843726 : Nat := 118140960795 + 843726 * 2 ^ 59
def prefixEnd_843726 : Nat := 4983230072969 + 3 ^ 40 * 843726 * 2
def baseEnd_843726 : Nat := 288824652463647434563187

theorem tailTrace_843726 : CollatzResearch.WordTrace tailWord_843726 prefixEnd_843726 288824652463647434563187 := by
  unfold tailWord_843726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3846651917666534221720879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20515476894221515849178021 3846651917666534221720879)
  ·
    refine ⟨5769977876499801332581319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3846651917666534221720879 5769977876499801332581319)
    ·
      refine ⟨8654966814749701998871979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5769977876499801332581319 8654966814749701998871979)
      ·
        refine ⟨12982450222124552998307969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8654966814749701998871979 12982450222124552998307969)
        ·
          refine ⟨9736837666593414748730977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12982450222124552998307969 9736837666593414748730977)
          ·
            refine ⟨7302628249945061061548233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9736837666593414748730977 7302628249945061061548233)
            ·
              refine ⟨5476971187458795796161175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7302628249945061061548233 5476971187458795796161175)
              ·
                refine ⟨8215456781188193694241763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5476971187458795796161175 8215456781188193694241763)
                ·
                  refine ⟨12323185171782290541362645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8215456781188193694241763 12323185171782290541362645)
                  ·
                    refine ⟨288824652463647434563187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12323185171782290541362645 288824652463647434563187)
                    ·
                      rfl

theorem cell22_843726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_843726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843726 prefixEnd_843726 := by exact prefixLift 843726
  have htrace : WordTrace (prefixWord ++ tailWord_843726) baseStart_843726 baseEnd_843726 := by
    simpa [prefixWord, tailWord_843726, baseEnd_843726] using wordTrace_append hprefix tailTrace_843726
  have hstable : (prefixWord ++ tailWord_843726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843726).length < 2 ^ (prefixWord ++ tailWord_843726).sum := by decide
  have hdescent : baseEnd_843726 < baseStart_843726 := by decide
  rcases family_descends (prefixWord ++ tailWord_843726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843728 : List Nat := [2, 1, 1, 1, 1, 2, 8, 1, 5]
def baseStart_843728 : Nat := 118140960795 + 843728 * 2 ^ 59
def prefixEnd_843728 : Nat := 4983230072969 + 3 ^ 40 * 843728 * 2
def baseEnd_843728 : Nat := 96275112368173365337727

theorem tailTrace_843728 : CollatzResearch.WordTrace tailWord_843728 prefixEnd_843728 96275112368173365337727 := by
  unfold tailWord_843728
  simp only [CollatzResearch.WordTrace]
  refine ⟨15386644143662514057669919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20515525524883352076893225 15386644143662514057669919)
  ·
    refine ⟨23079966215493771086504879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15386644143662514057669919 23079966215493771086504879)
    ·
      refine ⟨34619949323240656629757319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23079966215493771086504879 34619949323240656629757319)
      ·
        refine ⟨51929923984860984944635979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34619949323240656629757319 51929923984860984944635979)
        ·
          refine ⟨77894885977291477416953969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51929923984860984944635979 77894885977291477416953969)
          ·
            refine ⟨58421164482968608062715477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77894885977291477416953969 58421164482968608062715477)
            ·
              refine ⟨684623021284788375734947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 58421164482968608062715477 684623021284788375734947)
              ·
                refine ⟨1026934531927182563602421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684623021284788375734947 1026934531927182563602421)
                ·
                  refine ⟨96275112368173365337727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1026934531927182563602421 96275112368173365337727)
                  ·
                    rfl

theorem cell22_843728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 5].length) (baseStart_843728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843728 prefixEnd_843728 := by exact prefixLift 843728
  have htrace : WordTrace (prefixWord ++ tailWord_843728) baseStart_843728 baseEnd_843728 := by
    simpa [prefixWord, tailWord_843728, baseEnd_843728] using wordTrace_append hprefix tailTrace_843728
  have hstable : (prefixWord ++ tailWord_843728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843728).length < 2 ^ (prefixWord ++ tailWord_843728).sum := by decide
  have hdescent : baseEnd_843728 < baseStart_843728 := by decide
  rcases family_descends (prefixWord ++ tailWord_843728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843766 : List Nat := [5, 1, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_843766 : Nat := 118140960795 + 843766 * 2 ^ 59
def prefixEnd_843766 : Nat := 4983230072969 + 3 ^ 40 * 843766 * 2
def baseEnd_843766 : Nat := 288838345281100663563065

theorem tailTrace_843766 : CollatzResearch.WordTrace tailWord_843766 prefixEnd_843766 288838345281100663563065 := by
  unfold tailWord_843766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1923417141324210037826447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20516449507458240403482101 1923417141324210037826447)
  ·
    refine ⟨2885125711986315056739671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1923417141324210037826447 2885125711986315056739671)
    ·
      refine ⟨4327688567979472585109507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2885125711986315056739671 4327688567979472585109507)
      ·
        refine ⟨6491532851969208877664261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4327688567979472585109507 6491532851969208877664261)
        ·
          refine ⟨1217162409744226664562049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6491532851969208877664261 1217162409744226664562049)
          ·
            refine ⟨912871807308169998421537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1217162409744226664562049 912871807308169998421537)
            ·
              refine ⟨684653855481127498816153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 912871807308169998421537 684653855481127498816153)
              ·
                refine ⟨513490391610845624112115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684653855481127498816153 513490391610845624112115)
                ·
                  refine ⟨770235587416268436168173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513490391610845624112115 770235587416268436168173)
                  ·
                    refine ⟨288838345281100663563065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 770235587416268436168173 288838345281100663563065)
                    ·
                      rfl

theorem cell22_843766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_843766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843766 prefixEnd_843766 := by exact prefixLift 843766
  have htrace : WordTrace (prefixWord ++ tailWord_843766) baseStart_843766 baseEnd_843766 := by
    simpa [prefixWord, tailWord_843766, baseEnd_843766] using wordTrace_append hprefix tailTrace_843766
  have hstable : (prefixWord ++ tailWord_843766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843766).length < 2 ^ (prefixWord ++ tailWord_843766).sum := by decide
  have hdescent : baseEnd_843766 < baseStart_843766 := by decide
  rcases family_descends (prefixWord ++ tailWord_843766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843788 : List Nat := [2, 2, 1, 2, 3, 1, 4, 1, 1, 5]
def baseStart_843788 : Nat := 118140960795 + 843788 * 2 ^ 59
def prefixEnd_843788 : Nat := 4983230072969 + 3 ^ 40 * 843788 * 2
def baseEnd_843788 : Nat := 288845876330699939512997

theorem tailTrace_843788 : CollatzResearch.WordTrace tailWord_843788 prefixEnd_843788 288845876330699939512997 := by
  unfold tailWord_843788
  simp only [CollatzResearch.WordTrace]
  refine ⟨15387738333553829181262009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20516984444738438908349345 15387738333553829181262009)
  ·
    refine ⟨11540803750165371885946507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15387738333553829181262009 11540803750165371885946507)
    ·
      refine ⟨17311205625248057828919761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11540803750165371885946507 17311205625248057828919761)
      ·
        refine ⟨12983404218936043371689821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17311205625248057828919761 12983404218936043371689821)
        ·
          refine ⟨4868776582101016264383683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12983404218936043371689821 4868776582101016264383683)
          ·
            refine ⟨7303164873151524396575525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4868776582101016264383683 7303164873151524396575525)
            ·
              refine ⟨1369343413715910824357911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7303164873151524396575525 1369343413715910824357911)
              ·
                refine ⟨2054015120573866236536867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1369343413715910824357911 2054015120573866236536867)
                ·
                  refine ⟨3081022680860799354805301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2054015120573866236536867 3081022680860799354805301)
                  ·
                    refine ⟨288845876330699939512997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3081022680860799354805301 288845876330699939512997)
                    ·
                      rfl

theorem cell22_843788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_843788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843788 prefixEnd_843788 := by exact prefixLift 843788
  have htrace : WordTrace (prefixWord ++ tailWord_843788) baseStart_843788 baseEnd_843788 := by
    simpa [prefixWord, tailWord_843788, baseEnd_843788] using wordTrace_append hprefix tailTrace_843788
  have hstable : (prefixWord ++ tailWord_843788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843788).length < 2 ^ (prefixWord ++ tailWord_843788).sum := by decide
  have hdescent : baseEnd_843788 < baseStart_843788 := by decide
  rcases family_descends (prefixWord ++ tailWord_843788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843809 : List Nat := [1, 2, 3, 2, 5, 1, 2, 1, 1, 4]
def baseStart_843809 : Nat := 118140960795 + 843809 * 2 ^ 59
def prefixEnd_843809 : Nat := 4983230072969 + 3 ^ 40 * 843809 * 2
def baseEnd_843809 : Nat := 288853065059862884737933

theorem tailTrace_843809 : CollatzResearch.WordTrace tailWord_843809 prefixEnd_843809 288853065059862884737933 := by
  unfold tailWord_843809
  simp only [CollatzResearch.WordTrace]
  refine ⟨30776242600031578949038481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20517495066687719299358987 30776242600031578949038481)
  ·
    refine ⟨23082181950023684211778861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30776242600031578949038481 23082181950023684211778861)
    ·
      refine ⟨8655818231258881579417073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23082181950023684211778861 8655818231258881579417073)
      ·
        refine ⟨6491863673444161184562805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8655818231258881579417073 6491863673444161184562805)
        ·
          refine ⟨608612219385390111052763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6491863673444161184562805 608612219385390111052763)
          ·
            refine ⟨912918329078085166579145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608612219385390111052763 912918329078085166579145)
            ·
              refine ⟨684688746808563874934359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 912918329078085166579145 684688746808563874934359)
              ·
                refine ⟨1027033120212845812401539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684688746808563874934359 1027033120212845812401539)
                ·
                  refine ⟨1540549680319268718602309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1027033120212845812401539 1540549680319268718602309)
                  ·
                    refine ⟨288853065059862884737933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1540549680319268718602309 288853065059862884737933)
                    ·
                      rfl

theorem cell22_843809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_843809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843809 prefixEnd_843809 := by exact prefixLift 843809
  have htrace : WordTrace (prefixWord ++ tailWord_843809) baseStart_843809 baseEnd_843809 := by
    simpa [prefixWord, tailWord_843809, baseEnd_843809] using wordTrace_append hprefix tailTrace_843809
  have hstable : (prefixWord ++ tailWord_843809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843809).length < 2 ^ (prefixWord ++ tailWord_843809).sum := by decide
  have hdescent : baseEnd_843809 < baseStart_843809 := by decide
  rcases family_descends (prefixWord ++ tailWord_843809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843818 : List Nat := [3, 1, 4, 1, 2, 2, 9]
def baseStart_843818 : Nat := 118140960795 + 843818 * 2 ^ 59
def prefixEnd_843818 : Nat := 4983230072969 + 3 ^ 40 * 843818 * 2
def baseEnd_843818 : Nat := 10698375775695920787515

theorem tailTrace_843818 : CollatzResearch.WordTrace tailWord_843818 prefixEnd_843818 10698375775695920787515 := by
  unfold tailWord_843818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7694142714249743371529027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20517713904665982324077405 7694142714249743371529027)
  ·
    refine ⟨11541214071374615057293541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7694142714249743371529027 11541214071374615057293541)
    ·
      refine ⟨2163977638382740323242539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11541214071374615057293541 2163977638382740323242539)
      ·
        refine ⟨3245966457574110484863809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2163977638382740323242539 3245966457574110484863809)
        ·
          refine ⟨2434474843180582863647857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3245966457574110484863809 2434474843180582863647857)
          ·
            refine ⟨1825856132385437147735893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2434474843180582863647857 1825856132385437147735893)
            ·
              refine ⟨10698375775695920787515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1825856132385437147735893 10698375775695920787515)
              ·
                rfl

theorem cell22_843818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 9].length) (baseStart_843818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843818 prefixEnd_843818 := by exact prefixLift 843818
  have htrace : WordTrace (prefixWord ++ tailWord_843818) baseStart_843818 baseEnd_843818 := by
    simpa [prefixWord, tailWord_843818, baseEnd_843818] using wordTrace_append hprefix tailTrace_843818
  have hstable : (prefixWord ++ tailWord_843818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843818).length < 2 ^ (prefixWord ++ tailWord_843818).sum := by decide
  have hdescent : baseEnd_843818 < baseStart_843818 := by decide
  rcases family_descends (prefixWord ++ tailWord_843818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843822 : List Nat := [4, 1, 3, 1, 1, 2, 3, 2, 2, 3]
def baseStart_843822 : Nat := 118140960795 + 843822 * 2 ^ 59
def prefixEnd_843822 : Nat := 4983230072969 + 3 ^ 40 * 843822 * 2
def baseEnd_843822 : Nat := 288857515225535184162893

theorem tailTrace_843822 : CollatzResearch.WordTrace tailWord_843822 prefixEnd_843822 288857515225535184162893 := by
  unfold tailWord_843822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3847089593623060271157715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20517811165989654779507813 3847089593623060271157715)
  ·
    refine ⟨5770634390434590406736573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3847089593623060271157715 5770634390434590406736573)
    ·
      refine ⟨2163987896412971402526215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5770634390434590406736573 2163987896412971402526215)
      ·
        refine ⟨3245981844619457103789323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2163987896412971402526215 3245981844619457103789323)
        ·
          refine ⟨4868972766929185655683985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3245981844619457103789323 4868972766929185655683985)
          ·
            refine ⟨3651729575196889241762989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4868972766929185655683985 3651729575196889241762989)
            ·
              refine ⟨1369398590698833465661121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3651729575196889241762989 1369398590698833465661121)
              ·
                refine ⟨1027048943024125099245841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1369398590698833465661121 1027048943024125099245841)
                ·
                  refine ⟨770286707268093824434381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1027048943024125099245841 770286707268093824434381)
                  ·
                    refine ⟨288857515225535184162893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 770286707268093824434381 288857515225535184162893)
                    ·
                      rfl

theorem cell22_843822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_843822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843822 prefixEnd_843822 := by exact prefixLift 843822
  have htrace : WordTrace (prefixWord ++ tailWord_843822) baseStart_843822 baseEnd_843822 := by
    simpa [prefixWord, tailWord_843822, baseEnd_843822] using wordTrace_append hprefix tailTrace_843822
  have hstable : (prefixWord ++ tailWord_843822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843822).length < 2 ^ (prefixWord ++ tailWord_843822).sum := by decide
  have hdescent : baseEnd_843822 < baseStart_843822 := by decide
  rcases family_descends (prefixWord ++ tailWord_843822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843831 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 1, 8]
def baseStart_843831 : Nat := 118140960795 + 843831 * 2 ^ 59
def prefixEnd_843831 : Nat := 4983230072969 + 3 ^ 40 * 843831 * 2
def baseEnd_843831 : Nat := 288860596109462160687865

theorem tailTrace_843831 : CollatzResearch.WordTrace tailWord_843831 prefixEnd_843831 288860596109462160687865 := by
  unfold tailWord_843831
  simp only [CollatzResearch.WordTrace]
  refine ⟨30777045005951876706339347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20518030003967917804226231 30777045005951876706339347)
  ·
    refine ⟨46165567508927815059509021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30777045005951876706339347 46165567508927815059509021)
    ·
      refine ⟨17312087815847930647315883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46165567508927815059509021 17312087815847930647315883)
      ·
        refine ⟨25968131723771895970973825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17312087815847930647315883 25968131723771895970973825)
        ·
          refine ⟨19476098792828921978230369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25968131723771895970973825 19476098792828921978230369)
          ·
            refine ⟨14607074094621691483672777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19476098792828921978230369 14607074094621691483672777)
            ·
              refine ⟨10955305570966268612754583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14607074094621691483672777 10955305570966268612754583)
              ·
                refine ⟨16432958356449402919131875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10955305570966268612754583 16432958356449402919131875)
                ·
                  refine ⟨24649437534674104378697813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16432958356449402919131875 24649437534674104378697813)
                  ·
                    refine ⟨288860596109462160687865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24649437534674104378697813 288860596109462160687865)
                    ·
                      rfl

theorem cell22_843831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_843831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843831 prefixEnd_843831 := by exact prefixLift 843831
  have htrace : WordTrace (prefixWord ++ tailWord_843831) baseStart_843831 baseEnd_843831 := by
    simpa [prefixWord, tailWord_843831, baseEnd_843831] using wordTrace_append hprefix tailTrace_843831
  have hstable : (prefixWord ++ tailWord_843831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843831).length < 2 ^ (prefixWord ++ tailWord_843831).sum := by decide
  have hdescent : baseEnd_843831 < baseStart_843831 := by decide
  rcases family_descends (prefixWord ++ tailWord_843831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843884 : List Nat := [2, 2, 1, 1, 3, 4, 3, 2, 1, 3]
def baseStart_843884 : Nat := 118140960795 + 843884 * 2 ^ 59
def prefixEnd_843884 : Nat := 4983230072969 + 3 ^ 40 * 843884 * 2
def baseEnd_843884 : Nat := 288878739092587689112703

theorem tailTrace_843884 : CollatzResearch.WordTrace tailWord_843884 prefixEnd_843884 288878739092587689112703 := by
  unfold tailWord_843884
  simp only [CollatzResearch.WordTrace]
  refine ⟨15389489037379933379009353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20519318716506577838679137 15389489037379933379009353)
  ·
    refine ⟨11542116778034950034257015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15389489037379933379009353 11542116778034950034257015)
    ·
      refine ⟨17313175167052425051385523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11542116778034950034257015 17313175167052425051385523)
      ·
        refine ⟨25969762750578637577078285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17313175167052425051385523 25969762750578637577078285)
        ·
          refine ⟨9738661031466989091404357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25969762750578637577078285 9738661031466989091404357)
          ·
            refine ⟨1825998943400060454638317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9738661031466989091404357 1825998943400060454638317)
            ·
              refine ⟨684749603775022670489369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1825998943400060454638317 684749603775022670489369)
              ·
                refine ⟨513562202831267002867027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684749603775022670489369 513562202831267002867027)
                ·
                  refine ⟨770343304246900504300541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513562202831267002867027 770343304246900504300541)
                  ·
                    refine ⟨288878739092587689112703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 770343304246900504300541 288878739092587689112703)
                    ·
                      rfl

theorem cell22_843884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 1, 3].length) (baseStart_843884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843884 prefixEnd_843884 := by exact prefixLift 843884
  have htrace : WordTrace (prefixWord ++ tailWord_843884) baseStart_843884 baseEnd_843884 := by
    simpa [prefixWord, tailWord_843884, baseEnd_843884] using wordTrace_append hprefix tailTrace_843884
  have hstable : (prefixWord ++ tailWord_843884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843884).length < 2 ^ (prefixWord ++ tailWord_843884).sum := by decide
  have hdescent : baseEnd_843884 < baseStart_843884 := by decide
  rcases family_descends (prefixWord ++ tailWord_843884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843897 : List Nat := [1, 2, 1, 3, 4, 3, 2, 1, 5]
def baseStart_843897 : Nat := 118140960795 + 843897 * 2 ^ 59
def prefixEnd_843897 : Nat := 4983230072969 + 3 ^ 40 * 843897 * 2
def baseEnd_843897 : Nat := 96294396419419996179221

theorem tailTrace_843897 : CollatzResearch.WordTrace tailWord_843897 prefixEnd_843897 96294396419419996179221 := by
  unfold tailWord_843897
  simp only [CollatzResearch.WordTrace]
  refine ⟨30779452223712769978241945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20519634815808513318827963 30779452223712769978241945)
  ·
    refine ⟨23084589167784577483681459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30779452223712769978241945 23084589167784577483681459)
    ·
      refine ⟨34626883751676866225522189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23084589167784577483681459 34626883751676866225522189)
      ·
        refine ⟨12985081406878824834570821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34626883751676866225522189 12985081406878824834570821)
        ·
          refine ⟨2434702763789779656482029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12985081406878824834570821 2434702763789779656482029)
          ·
            refine ⟨913013536421167371180761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2434702763789779656482029 913013536421167371180761)
            ·
              refine ⟨684760152315875528385571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 913013536421167371180761 684760152315875528385571)
              ·
                refine ⟨1027140228473813292578357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684760152315875528385571 1027140228473813292578357)
                ·
                  refine ⟨96294396419419996179221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1027140228473813292578357 96294396419419996179221)
                  ·
                    rfl

theorem cell22_843897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 5].length) (baseStart_843897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843897 prefixEnd_843897 := by exact prefixLift 843897
  have htrace : WordTrace (prefixWord ++ tailWord_843897) baseStart_843897 baseEnd_843897 := by
    simpa [prefixWord, tailWord_843897, baseEnd_843897] using wordTrace_append hprefix tailTrace_843897
  have hstable : (prefixWord ++ tailWord_843897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843897).length < 2 ^ (prefixWord ++ tailWord_843897).sum := by decide
  have hdescent : baseEnd_843897 < baseStart_843897 := by decide
  rcases family_descends (prefixWord ++ tailWord_843897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843908 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 8]
def baseStart_843908 : Nat := 118140960795 + 843908 * 2 ^ 59
def prefixEnd_843908 : Nat := 4983230072969 + 3 ^ 40 * 843908 * 2
def baseEnd_843908 : Nat := 96295651594353208837543

theorem tailTrace_843908 : CollatzResearch.WordTrace tailWord_843908 prefixEnd_843908 96295651594353208837543 := by
  unfold tailWord_843908
  simp only [CollatzResearch.WordTrace]
  refine ⟨15389926713336459428446189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20519902284448612571261585 15389926713336459428446189)
  ·
    refine ⟨5771222517501172285667321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15389926713336459428446189 5771222517501172285667321)
    ·
      refine ⟨4328416888125879214250491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5771222517501172285667321 4328416888125879214250491)
      ·
        refine ⟨6492625332188818821375737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4328416888125879214250491 6492625332188818821375737)
        ·
          refine ⟨4869468999141614116031803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6492625332188818821375737 4869468999141614116031803)
          ·
            refine ⟨7304203498712421174047705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4869468999141614116031803 7304203498712421174047705)
            ·
              refine ⟨5478152624034315880535779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7304203498712421174047705 5478152624034315880535779)
              ·
                refine ⟨8217228936051473820803669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5478152624034315880535779 8217228936051473820803669)
                ·
                  refine ⟨96295651594353208837543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8217228936051473820803669 96295651594353208837543)
                  ·
                    rfl

theorem cell22_843908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_843908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843908 prefixEnd_843908 := by exact prefixLift 843908
  have htrace : WordTrace (prefixWord ++ tailWord_843908) baseStart_843908 baseEnd_843908 := by
    simpa [prefixWord, tailWord_843908, baseEnd_843908] using wordTrace_append hprefix tailTrace_843908
  have hstable : (prefixWord ++ tailWord_843908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843908).length < 2 ^ (prefixWord ++ tailWord_843908).sum := by decide
  have hdescent : baseEnd_843908 < baseStart_843908 := by decide
  rcases family_descends (prefixWord ++ tailWord_843908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843925 : List Nat := [1, 3, 2, 1, 1, 1, 4, 5, 4]
def baseStart_843925 : Nat := 118140960795 + 843925 * 2 ^ 59
def prefixEnd_843925 : Nat := 4983230072969 + 3 ^ 40 * 843925 * 2
def baseEnd_843925 : Nat := 96297591410159082945859

theorem tailTrace_843925 : CollatzResearch.WordTrace tailWord_843925 prefixEnd_843925 96297591410159082945859 := by
  unfold tailWord_843925
  simp only [CollatzResearch.WordTrace]
  refine ⟨30780473467611330760261229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20520315645074220506840819 30780473467611330760261229)
  ·
    refine ⟨11542677550354249035097961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30780473467611330760261229 11542677550354249035097961)
    ·
      refine ⟨8657008162765686776323471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11542677550354249035097961 8657008162765686776323471)
      ·
        refine ⟨12985512244148530164485207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8657008162765686776323471 12985512244148530164485207)
        ·
          refine ⟨19478268366222795246727811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12985512244148530164485207 19478268366222795246727811)
          ·
            refine ⟨29217402549334192870091717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19478268366222795246727811 29217402549334192870091717)
            ·
              refine ⟨5478262978000161163142197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29217402549334192870091717 5478262978000161163142197)
              ·
                refine ⟨513587154187515109044581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5478262978000161163142197 513587154187515109044581)
                ·
                  refine ⟨96297591410159082945859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 513587154187515109044581 96297591410159082945859)
                  ·
                    rfl

theorem cell22_843925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_843925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843925 prefixEnd_843925 := by exact prefixLift 843925
  have htrace : WordTrace (prefixWord ++ tailWord_843925) baseStart_843925 baseEnd_843925 := by
    simpa [prefixWord, tailWord_843925, baseEnd_843925] using wordTrace_append hprefix tailTrace_843925
  have hstable : (prefixWord ++ tailWord_843925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843925).length < 2 ^ (prefixWord ++ tailWord_843925).sum := by decide
  have hdescent : baseEnd_843925 < baseStart_843925 := by decide
  rcases family_descends (prefixWord ++ tailWord_843925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843972 : List Nat := [2, 3, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_843972 : Nat := 118140960795 + 843972 * 2 ^ 59
def prefixEnd_843972 : Nat := 4983230072969 + 3 ^ 40 * 843972 * 2
def baseEnd_843972 : Nat := 288908863290984792912433

theorem tailTrace_843972 : CollatzResearch.WordTrace tailWord_843972 prefixEnd_843972 288908863290984792912433 := by
  unfold tailWord_843972
  simp only [CollatzResearch.WordTrace]
  refine ⟨15391093849220528893611085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20521458465627371858148113 15391093849220528893611085)
  ·
    refine ⟨5771660193457698335104157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15391093849220528893611085 5771660193457698335104157)
    ·
      refine ⟨2164372572546636875664059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5771660193457698335104157 2164372572546636875664059)
      ·
        refine ⟨3246558858819955313496089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2164372572546636875664059 3246558858819955313496089)
        ·
          refine ⟨2434919144114966485122067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3246558858819955313496089 2434919144114966485122067)
          ·
            refine ⟨3652378716172449727683101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2434919144114966485122067 3652378716172449727683101)
            ·
              refine ⟨1369642018564668647881163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3652378716172449727683101 1369642018564668647881163)
              ·
                refine ⟨2054463027847002971821745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1369642018564668647881163 2054463027847002971821745)
                ·
                  refine ⟨1540847270885252228866309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2054463027847002971821745 1540847270885252228866309)
                  ·
                    refine ⟨288908863290984792912433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1540847270885252228866309 288908863290984792912433)
                    ·
                      rfl

theorem cell22_843972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_843972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_843972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_843972 prefixEnd_843972 := by exact prefixLift 843972
  have htrace : WordTrace (prefixWord ++ tailWord_843972) baseStart_843972 baseEnd_843972 := by
    simpa [prefixWord, tailWord_843972, baseEnd_843972] using wordTrace_append hprefix tailTrace_843972
  have hstable : (prefixWord ++ tailWord_843972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843972).length < 2 ^ (prefixWord ++ tailWord_843972).sum := by decide
  have hdescent : baseEnd_843972 < baseStart_843972 := by decide
  rcases family_descends (prefixWord ++ tailWord_843972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844137 : List Nat := [1, 2, 1, 1, 1, 3, 5, 2, 3, 3]
def baseStart_844137 : Nat := 118140960795 + 844137 * 2 ^ 59
def prefixEnd_844137 : Nat := 4983230072969 + 3 ^ 40 * 844137 * 2
def baseEnd_844137 : Nat := 288965346162979362536927

theorem tailTrace_844137 : CollatzResearch.WordTrace tailWord_844137 prefixEnd_844137 288965346162979362536927 := by
  unfold tailWord_844137
  simp only [CollatzResearch.WordTrace]
  refine ⟨30788205742843290966978665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20525470495228860644652443 30788205742843290966978665)
  ·
    refine ⟨23091154307132468225233999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30788205742843290966978665 23091154307132468225233999)
    ·
      refine ⟨34636731460698702337850999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23091154307132468225233999 34636731460698702337850999)
      ·
        refine ⟨51955097191048053506776499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34636731460698702337850999 51955097191048053506776499)
        ·
          refine ⟨77932645786572080260164749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51955097191048053506776499 77932645786572080260164749)
          ·
            refine ⟨29224742169964530097561781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77932645786572080260164749 29224742169964530097561781)
            ·
              refine ⟨2739819578434174696646417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29224742169964530097561781 2739819578434174696646417)
              ·
                refine ⟨2054864683825631022484813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2739819578434174696646417 2054864683825631022484813)
                ·
                  refine ⟨770574256434611633431805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2054864683825631022484813 770574256434611633431805)
                  ·
                    refine ⟨288965346162979362536927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 770574256434611633431805 288965346162979362536927)
                    ·
                      rfl

theorem cell22_844137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 3].length) (baseStart_844137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_844137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_844137 prefixEnd_844137 := by exact prefixLift 844137
  have htrace : WordTrace (prefixWord ++ tailWord_844137) baseStart_844137 baseEnd_844137 := by
    simpa [prefixWord, tailWord_844137, baseEnd_844137] using wordTrace_append hprefix tailTrace_844137
  have hstable : (prefixWord ++ tailWord_844137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844137).length < 2 ^ (prefixWord ++ tailWord_844137).sum := by decide
  have hdescent : baseEnd_844137 < baseStart_844137 := by decide
  rcases family_descends (prefixWord ++ tailWord_844137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844205 : List Nat := [1, 5, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_844205 : Nat := 118140960795 + 844205 * 2 ^ 59
def prefixEnd_844205 : Nat := 4983230072969 + 3 ^ 40 * 844205 * 2
def baseEnd_844205 : Nat := 288988623952649851836719

theorem tailTrace_844205 : CollatzResearch.WordTrace tailWord_844205 prefixEnd_844205 288988623952649851836719 := by
  unfold tailWord_844205
  simp only [CollatzResearch.WordTrace]
  refine ⟨30790685906596938580454069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20527123937731292386969379 30790685906596938580454069)
  ·
    refine ⟨2886626803743462991917569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30790685906596938580454069 2886626803743462991917569)
    ·
      refine ⟨2164970102807597243938177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2886626803743462991917569 2164970102807597243938177)
      ·
        refine ⟨1623727577105697932953633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2164970102807597243938177 1623727577105697932953633)
        ·
          refine ⟨1217795682829273449715225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1623727577105697932953633 1217795682829273449715225)
          ·
            refine ⟨913346762121955087286419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1217795682829273449715225 913346762121955087286419)
            ·
              refine ⟨1370020143182932630929629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913346762121955087286419 1370020143182932630929629)
              ·
                refine ⟨513757553693599736598611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1370020143182932630929629 513757553693599736598611)
                ·
                  refine ⟨770636330540399604897917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513757553693599736598611 770636330540399604897917)
                  ·
                    refine ⟨288988623952649851836719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 770636330540399604897917 288988623952649851836719)
                    ·
                      rfl

theorem cell22_844205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_844205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_844205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_844205 prefixEnd_844205 := by exact prefixLift 844205
  have htrace : WordTrace (prefixWord ++ tailWord_844205) baseStart_844205 baseEnd_844205 := by
    simpa [prefixWord, tailWord_844205, baseEnd_844205] using wordTrace_append hprefix tailTrace_844205
  have hstable : (prefixWord ++ tailWord_844205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844205).length < 2 ^ (prefixWord ++ tailWord_844205).sum := by decide
  have hdescent : baseEnd_844205 < baseStart_844205 := by decide
  rcases family_descends (prefixWord ++ tailWord_844205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844274 : List Nat := [3, 2, 1, 4, 3, 9]
def baseStart_844274 : Nat := 118140960795 + 844274 * 2 ^ 59
def prefixEnd_844274 : Nat := 4983230072969 + 3 ^ 40 * 844274 * 2
def baseEnd_844274 : Nat := 3568052395836502121747

theorem tailTrace_844274 : CollatzResearch.WordTrace tailWord_844274 prefixEnd_844274 3568052395836502121747 := by
  unfold tailWord_844274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7698300635836740841178969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20528801695564642243143917 7698300635836740841178969)
  ·
    refine ⟨5773725476877555630884227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7698300635836740841178969 5773725476877555630884227)
    ·
      refine ⟨8660588215316333446326341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5773725476877555630884227 8660588215316333446326341)
      ·
        refine ⟨1623860290371812521186189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8660588215316333446326341 1623860290371812521186189)
        ·
          refine ⟨608947608889429695444821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1623860290371812521186189 608947608889429695444821)
          ·
            refine ⟨3568052395836502121747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 608947608889429695444821 3568052395836502121747)
            ·
              rfl

theorem cell22_844274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 9].length) (baseStart_844274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_844274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_844274 prefixEnd_844274 := by exact prefixLift 844274
  have htrace : WordTrace (prefixWord ++ tailWord_844274) baseStart_844274 baseEnd_844274 := by
    simpa [prefixWord, tailWord_844274, baseEnd_844274] using wordTrace_append hprefix tailTrace_844274
  have hstable : (prefixWord ++ tailWord_844274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844274).length < 2 ^ (prefixWord ++ tailWord_844274).sum := by decide
  have hdescent : baseEnd_844274 < baseStart_844274 := by decide
  rcases family_descends (prefixWord ++ tailWord_844274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844323 : List Nat := [1, 1, 1, 4, 4, 2, 2, 3, 1, 3]
def baseStart_844323 : Nat := 118140960795 + 844323 * 2 ^ 59
def prefixEnd_844323 : Nat := 4983230072969 + 3 ^ 40 * 844323 * 2
def baseEnd_844323 : Nat := 289029017764136877386357

theorem tailTrace_844323 : CollatzResearch.WordTrace tailWord_844323 prefixEnd_844323 289029017764136877386357 := by
  unfold tailWord_844323
  simp only [CollatzResearch.WordTrace]
  refine ⟨30794989720169444733249623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20529993146779629822166415 30794989720169444733249623)
  ·
    refine ⟨46192484580254167099874435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30794989720169444733249623 46192484580254167099874435)
    ·
      refine ⟨69288726870381250649811653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46192484580254167099874435 69288726870381250649811653)
      ·
        refine ⟨12991636288196484496839685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69288726870381250649811653 12991636288196484496839685)
        ·
          refine ⟨2435931804036840843157441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12991636288196484496839685 2435931804036840843157441)
          ·
            refine ⟨1826948853027630632368081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2435931804036840843157441 1826948853027630632368081)
            ·
              refine ⟨1370211639770722974276061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1826948853027630632368081 1370211639770722974276061)
              ·
                refine ⟨513829364914021115353523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1370211639770722974276061 513829364914021115353523)
                ·
                  refine ⟨770744047371031673030285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513829364914021115353523 770744047371031673030285)
                  ·
                    refine ⟨289029017764136877386357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 770744047371031673030285 289029017764136877386357)
                    ·
                      rfl

theorem cell22_844323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 1, 3].length) (baseStart_844323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_844323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_844323 prefixEnd_844323 := by exact prefixLift 844323
  have htrace : WordTrace (prefixWord ++ tailWord_844323) baseStart_844323 baseEnd_844323 := by
    simpa [prefixWord, tailWord_844323, baseEnd_844323] using wordTrace_append hprefix tailTrace_844323
  have hstable : (prefixWord ++ tailWord_844323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844323).length < 2 ^ (prefixWord ++ tailWord_844323).sum := by decide
  have hdescent : baseEnd_844323 < baseStart_844323 := by decide
  rcases family_descends (prefixWord ++ tailWord_844323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844340 : List Nat := [2, 5, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_844340 : Nat := 118140960795 + 844340 * 2 ^ 59
def prefixEnd_844340 : Nat := 4983230072969 + 3 ^ 40 * 844340 * 2
def baseEnd_844340 : Nat := 289034837211554499711305

theorem tailTrace_844340 : CollatzResearch.WordTrace tailWord_844340 prefixEnd_844340 289034837211554499711305 := by
  unfold tailWord_844340
  simp only [CollatzResearch.WordTrace]
  refine ⟨15397804880553928318309237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20530406507405237757745649 15397804880553928318309237)
  ·
    refine ⟨1443544207551930779841491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15397804880553928318309237 1443544207551930779841491)
    ·
      refine ⟨2165316311327896169762237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1443544207551930779841491 2165316311327896169762237)
      ·
        refine ⟨811993616747961063660839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2165316311327896169762237 811993616747961063660839)
        ·
          refine ⟨1217990425121941595491259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811993616747961063660839 1217990425121941595491259)
          ·
            refine ⟨1826985637682912393236889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217990425121941595491259 1826985637682912393236889)
            ·
              refine ⟨1370239228262184294927667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1826985637682912393236889 1370239228262184294927667)
              ·
                refine ⟨2055358842393276442391501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370239228262184294927667 2055358842393276442391501)
                ·
                  refine ⟨770759565897478665896813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2055358842393276442391501 770759565897478665896813)
                  ·
                    refine ⟨289034837211554499711305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 770759565897478665896813 289034837211554499711305)
                    ·
                      rfl

theorem cell22_844340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_844340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_844340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_844340 prefixEnd_844340 := by exact prefixLift 844340
  have htrace : WordTrace (prefixWord ++ tailWord_844340) baseStart_844340 baseEnd_844340 := by
    simpa [prefixWord, tailWord_844340, baseEnd_844340] using wordTrace_append hprefix tailTrace_844340
  have hstable : (prefixWord ++ tailWord_844340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844340).length < 2 ^ (prefixWord ++ tailWord_844340).sum := by decide
  have hdescent : baseEnd_844340 < baseStart_844340 := by decide
  rcases family_descends (prefixWord ++ tailWord_844340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844409 : List Nat := [1, 2, 1, 3, 3, 3, 2, 7]
def baseStart_844409 : Nat := 118140960795 + 844409 * 2 ^ 59
def prefixEnd_844409 : Nat := 4983230072969 + 3 ^ 40 * 844409 * 2
def baseEnd_844409 : Nat := 32117606369073479970677

theorem tailTrace_844409 : CollatzResearch.WordTrace tailWord_844409 prefixEnd_844409 32117606369073479970677 := by
  unfold tailWord_844409
  simp only [CollatzResearch.WordTrace]
  refine ⟨30798126397857881420880281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20532084265238587613920187 30798126397857881420880281)
  ·
    refine ⟨23098594798393411065660211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30798126397857881420880281 23098594798393411065660211)
    ·
      refine ⟨34647892197590116598490317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23098594798393411065660211 34647892197590116598490317)
      ·
        refine ⟨12992959574096293724433869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34647892197590116598490317 12992959574096293724433869)
        ·
          refine ⟨4872359840286110146662701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12992959574096293724433869 4872359840286110146662701)
          ·
            refine ⟨1827134940107291304998513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4872359840286110146662701 1827134940107291304998513)
            ·
              refine ⟨1370351205080468478748885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1827134940107291304998513 1370351205080468478748885)
              ·
                refine ⟨32117606369073479970677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1370351205080468478748885 32117606369073479970677)
                ·
                  rfl

theorem cell22_844409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 7].length) (baseStart_844409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_844409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_844409 prefixEnd_844409 := by exact prefixLift 844409
  have htrace : WordTrace (prefixWord ++ tailWord_844409) baseStart_844409 baseEnd_844409 := by
    simpa [prefixWord, tailWord_844409, baseEnd_844409] using wordTrace_append hprefix tailTrace_844409
  have hstable : (prefixWord ++ tailWord_844409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844409).length < 2 ^ (prefixWord ++ tailWord_844409).sum := by decide
  have hdescent : baseEnd_844409 < baseStart_844409 := by decide
  rcases family_descends (prefixWord ++ tailWord_844409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844413 : List Nat := [1, 4, 1, 1, 5, 1, 1, 3, 2, 3]
def baseStart_844413 : Nat := 118140960795 + 844413 * 2 ^ 59
def prefixEnd_844413 : Nat := 4983230072969 + 3 ^ 40 * 844413 * 2
def baseEnd_844413 : Nat := 289059826603406642636081

theorem tailTrace_844413 : CollatzResearch.WordTrace tailWord_844413 prefixEnd_844413 289059826603406642636081 := by
  unfold tailWord_844413
  simp only [CollatzResearch.WordTrace]
  refine ⟨30798272289843390104025893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20532181526562260069350595 30798272289843390104025893)
  ·
    refine ⟨5774676054345635644504855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30798272289843390104025893 5774676054345635644504855)
    ·
      refine ⟨8662014081518453466757283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5774676054345635644504855 8662014081518453466757283)
      ·
        refine ⟨12993021122277680200135925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8662014081518453466757283 12993021122277680200135925)
        ·
          refine ⟨1218095730213532518762743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12993021122277680200135925 1218095730213532518762743)
          ·
            refine ⟨1827143595320298778144115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218095730213532518762743 1827143595320298778144115)
            ·
              refine ⟨2740715392980448167216173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1827143595320298778144115 2740715392980448167216173)
              ·
                refine ⟨1027768272367668062706065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2740715392980448167216173 1027768272367668062706065)
                ·
                  refine ⟨770826204275751047029549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1027768272367668062706065 770826204275751047029549)
                  ·
                    refine ⟨289059826603406642636081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 770826204275751047029549 289059826603406642636081)
                    ·
                      rfl

theorem cell22_844413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_844413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_844413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_844413 prefixEnd_844413 := by exact prefixLift 844413
  have htrace : WordTrace (prefixWord ++ tailWord_844413) baseStart_844413 baseEnd_844413 := by
    simpa [prefixWord, tailWord_844413, baseEnd_844413] using wordTrace_append hprefix tailTrace_844413
  have hstable : (prefixWord ++ tailWord_844413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844413).length < 2 ^ (prefixWord ++ tailWord_844413).sum := by decide
  have hdescent : baseEnd_844413 < baseStart_844413 := by decide
  rcases family_descends (prefixWord ++ tailWord_844413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844516 : List Nat := [2, 3, 1, 1, 1, 5, 2, 1, 6]
def baseStart_844516 : Nat := 118140960795 + 844516 * 2 ^ 59
def prefixEnd_844516 : Nat := 4983230072969 + 3 ^ 40 * 844516 * 2
def baseEnd_844516 : Nat := 96365028536116235770255

theorem tailTrace_844516 : CollatzResearch.WordTrace tailWord_844516 prefixEnd_844516 96365028536116235770255 := by
  unfold tailWord_844516
  simp only [CollatzResearch.WordTrace]
  refine ⟨15401014504235119347512701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20534686005646825796683601 15401014504235119347512701)
  ·
    refine ⟨5775380439088169755317263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15401014504235119347512701 5775380439088169755317263)
    ·
      refine ⟨8663070658632254632975895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5775380439088169755317263 8663070658632254632975895)
      ·
        refine ⟨12994605987948381949463843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8663070658632254632975895 12994605987948381949463843)
        ·
          refine ⟨19491908981922572924195765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12994605987948381949463843 19491908981922572924195765)
          ·
            refine ⟨1827366467055241211643353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19491908981922572924195765 1827366467055241211643353)
            ·
              refine ⟨1370524850291430908732515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1827366467055241211643353 1370524850291430908732515)
              ·
                refine ⟨2055787275437146363098773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370524850291430908732515 2055787275437146363098773)
                ·
                  refine ⟨96365028536116235770255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2055787275437146363098773 96365028536116235770255)
                  ·
                    rfl

theorem cell22_844516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_844516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_844516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_844516 prefixEnd_844516 := by exact prefixLift 844516
  have htrace : WordTrace (prefixWord ++ tailWord_844516) baseStart_844516 baseEnd_844516 := by
    simpa [prefixWord, tailWord_844516, baseEnd_844516] using wordTrace_append hprefix tailTrace_844516
  have hstable : (prefixWord ++ tailWord_844516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844516).length < 2 ^ (prefixWord ++ tailWord_844516).sum := by decide
  have hdescent : baseEnd_844516 < baseStart_844516 := by decide
  rcases family_descends (prefixWord ++ tailWord_844516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844529 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 3, 6]
def baseStart_844529 : Nat := 118140960795 + 844529 * 2 ^ 59
def prefixEnd_844529 : Nat := 4983230072969 + 3 ^ 40 * 844529 * 2
def baseEnd_844529 : Nat := 289099535774021006735725

theorem tailTrace_844529 : CollatzResearch.WordTrace tailWord_844529 prefixEnd_844529 289099535774021006735725 := by
  unfold tailWord_844529
  simp only [CollatzResearch.WordTrace]
  refine ⟨30802503157423141915248641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20535002104948761276832427 30802503157423141915248641)
  ·
    refine ⟨23101877368067356436436481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30802503157423141915248641 23101877368067356436436481)
    ·
      refine ⟨17326408026050517327327361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23101877368067356436436481 17326408026050517327327361)
      ·
        refine ⟨12994806019537887995495521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17326408026050517327327361 12994806019537887995495521)
        ·
          refine ⟨9746104514653415996621641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12994806019537887995495521 9746104514653415996621641)
          ·
            refine ⟨7309578385990061997466231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9746104514653415996621641 7309578385990061997466231)
            ·
              refine ⟨10964367578985092996199347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7309578385990061997466231 10964367578985092996199347)
              ·
                refine ⟨16446551368477639494299021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10964367578985092996199347 16446551368477639494299021)
                ·
                  refine ⟨6167456763179114810362133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16446551368477639494299021 6167456763179114810362133)
                  ·
                    refine ⟨289099535774021006735725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6167456763179114810362133 289099535774021006735725)
                    ·
                      rfl

theorem cell22_844529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_844529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_844529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_844529 prefixEnd_844529 := by exact prefixLift 844529
  have htrace : WordTrace (prefixWord ++ tailWord_844529) baseStart_844529 baseEnd_844529 := by
    simpa [prefixWord, tailWord_844529, baseEnd_844529] using wordTrace_append hprefix tailTrace_844529
  have hstable : (prefixWord ++ tailWord_844529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844529).length < 2 ^ (prefixWord ++ tailWord_844529).sum := by decide
  have hdescent : baseEnd_844529 < baseStart_844529 := by decide
  rcases family_descends (prefixWord ++ tailWord_844529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844653 : List Nat := [1, 5, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_844653 : Nat := 118140960795 + 844653 * 2 ^ 59
def prefixEnd_844653 : Nat := 4983230072969 + 3 ^ 40 * 844653 * 2
def baseEnd_844653 : Nat := 289141983508126016635345

theorem tailTrace_844653 : CollatzResearch.WordTrace tailWord_844653 prefixEnd_844653 289141983508126016635345 := by
  unfold tailWord_844653
  simp only [CollatzResearch.WordTrace]
  refine ⟨30807025808973911092762613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20538017205982607395175075 30807025808973911092762613)
  ·
    refine ⟨2888158669591304164946495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30807025808973911092762613 2888158669591304164946495)
    ·
      refine ⟨4332238004386956247419743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2888158669591304164946495 4332238004386956247419743)
      ·
        refine ⟨6498357006580434371129615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4332238004386956247419743 6498357006580434371129615)
        ·
          refine ⟨9747535509870651556694423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6498357006580434371129615 9747535509870651556694423)
          ·
            refine ⟨14621303264805977335041635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9747535509870651556694423 14621303264805977335041635)
            ·
              refine ⟨21931954897208966002562453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14621303264805977335041635 21931954897208966002562453)
              ·
                refine ⟨1028060385806670281370115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21931954897208966002562453 1028060385806670281370115)
                ·
                  refine ⟨1542090578710005422055173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028060385806670281370115 1542090578710005422055173)
                  ·
                    refine ⟨289141983508126016635345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1542090578710005422055173 289141983508126016635345)
                    ·
                      rfl

theorem cell22_844653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_844653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_844653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_844653 prefixEnd_844653 := by exact prefixLift 844653
  have htrace : WordTrace (prefixWord ++ tailWord_844653) baseStart_844653 baseEnd_844653 := by
    simpa [prefixWord, tailWord_844653, baseEnd_844653] using wordTrace_append hprefix tailTrace_844653
  have hstable : (prefixWord ++ tailWord_844653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844653).length < 2 ^ (prefixWord ++ tailWord_844653).sum := by decide
  have hdescent : baseEnd_844653 < baseStart_844653 := by decide
  rcases family_descends (prefixWord ++ tailWord_844653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844674 : List Nat := [3, 4, 2, 2, 1, 2, 1, 2, 5]
def baseStart_844674 : Nat := 118140960795 + 844674 * 2 ^ 59
def prefixEnd_844674 : Nat := 4983230072969 + 3 ^ 40 * 844674 * 2
def baseEnd_844674 : Nat := 96383057412429653953427

theorem tailTrace_844674 : CollatzResearch.WordTrace tailWord_844674 prefixEnd_844674 96383057412429653953427 := by
  unfold tailWord_844674
  simp only [CollatzResearch.WordTrace]
  refine ⟨7701947935474457919819269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20538527827931887786184717 7701947935474457919819269)
  ·
    refine ⟨1444115237901460859966113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7701947935474457919819269 1444115237901460859966113)
    ·
      refine ⟨1083086428426095644974585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1444115237901460859966113 1083086428426095644974585)
      ·
        refine ⟨812314821319571733730939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1083086428426095644974585 812314821319571733730939)
        ·
          refine ⟨1218472231979357600596409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812314821319571733730939 1218472231979357600596409)
          ·
            refine ⟨913854173984518200447307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1218472231979357600596409 913854173984518200447307)
            ·
              refine ⟨1370781260976777300670961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913854173984518200447307 1370781260976777300670961)
              ·
                refine ⟨1028085945732582975503221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1370781260976777300670961 1028085945732582975503221)
                ·
                  refine ⟨96383057412429653953427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1028085945732582975503221 96383057412429653953427)
                  ·
                    rfl

theorem cell22_844674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_844674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_844674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_844674 prefixEnd_844674 := by exact prefixLift 844674
  have htrace : WordTrace (prefixWord ++ tailWord_844674) baseStart_844674 baseEnd_844674 := by
    simpa [prefixWord, tailWord_844674, baseEnd_844674] using wordTrace_append hprefix tailTrace_844674
  have hstable : (prefixWord ++ tailWord_844674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844674).length < 2 ^ (prefixWord ++ tailWord_844674).sum := by decide
  have hdescent : baseEnd_844674 < baseStart_844674 := by decide
  rcases family_descends (prefixWord ++ tailWord_844674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844839 : List Nat := [1, 1, 7, 1, 1, 1, 4, 1, 1, 4]
def baseStart_844839 : Nat := 118140960795 + 844839 * 2 ^ 59
def prefixEnd_844839 : Nat := 4983230072969 + 3 ^ 40 * 844839 * 2
def baseEnd_844839 : Nat := 289205655109283531484775

theorem tailTrace_844839 : CollatzResearch.WordTrace tailWord_844839 prefixEnd_844839 289205655109283531484775 := by
  unfold tailWord_844839
  simp only [CollatzResearch.WordTrace]
  refine ⟨30813809786300064859033571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20542539857533376572689047 30813809786300064859033571)
  ·
    refine ⟨46220714679450097288550357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30813809786300064859033571 46220714679450097288550357)
    ·
      refine ⟨1083298000299611655200399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 46220714679450097288550357 1083298000299611655200399)
      ·
        refine ⟨1624947000449417482800599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1083298000299611655200399 1624947000449417482800599)
        ·
          refine ⟨2437420500674126224200899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1624947000449417482800599 2437420500674126224200899)
          ·
            refine ⟨3656130751011189336301349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2437420500674126224200899 3656130751011189336301349)
            ·
              refine ⟨685524515814598000556503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3656130751011189336301349 685524515814598000556503)
              ·
                refine ⟨1028286773721897000834755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685524515814598000556503 1028286773721897000834755)
                ·
                  refine ⟨1542430160582845501252133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028286773721897000834755 1542430160582845501252133)
                  ·
                    refine ⟨289205655109283531484775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1542430160582845501252133 289205655109283531484775)
                    ·
                      rfl

theorem cell22_844839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_844839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_844839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_844839 prefixEnd_844839 := by exact prefixLift 844839
  have htrace : WordTrace (prefixWord ++ tailWord_844839) baseStart_844839 baseEnd_844839 := by
    simpa [prefixWord, tailWord_844839, baseEnd_844839] using wordTrace_append hprefix tailTrace_844839
  have hstable : (prefixWord ++ tailWord_844839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844839).length < 2 ^ (prefixWord ++ tailWord_844839).sum := by decide
  have hdescent : baseEnd_844839 < baseStart_844839 := by decide
  rcases family_descends (prefixWord ++ tailWord_844839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844882 : List Nat := [3, 2, 2, 1, 3, 3, 2, 6]
def baseStart_844882 : Nat := 118140960795 + 844882 * 2 ^ 59
def prefixEnd_844882 : Nat := 4983230072969 + 3 ^ 40 * 844882 * 2
def baseEnd_844882 : Nat := 32135597209782861406627

theorem tailTrace_844882 : CollatzResearch.WordTrace tailWord_844882 prefixEnd_844882 32135597209782861406627 := by
  unfold tailWord_844882
  simp only [CollatzResearch.WordTrace]
  refine ⟨7703844531286070800712225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20543585416762855468565933 7703844531286070800712225)
  ·
    refine ⟨5777883398464553100534169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7703844531286070800712225 5777883398464553100534169)
    ·
      refine ⟨4333412548848414825400627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5777883398464553100534169 4333412548848414825400627)
      ·
        refine ⟨6500118823272622238100941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4333412548848414825400627 6500118823272622238100941)
        ·
          refine ⟨2437544558727233339287853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6500118823272622238100941 2437544558727233339287853)
          ·
            refine ⟨914079209522712502232945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2437544558727233339287853 914079209522712502232945)
            ·
              refine ⟨685559407142034376674709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 914079209522712502232945 685559407142034376674709)
              ·
                refine ⟨32135597209782861406627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 685559407142034376674709 32135597209782861406627)
                ·
                  rfl

theorem cell22_844882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 6].length) (baseStart_844882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_844882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_844882 prefixEnd_844882 := by exact prefixLift 844882
  have htrace : WordTrace (prefixWord ++ tailWord_844882) baseStart_844882 baseEnd_844882 := by
    simpa [prefixWord, tailWord_844882, baseEnd_844882] using wordTrace_append hprefix tailTrace_844882
  have hstable : (prefixWord ++ tailWord_844882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844882).length < 2 ^ (prefixWord ++ tailWord_844882).sum := by decide
  have hdescent : baseEnd_844882 < baseStart_844882 := by decide
  rcases family_descends (prefixWord ++ tailWord_844882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844910 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 7]
def baseStart_844910 : Nat := 118140960795 + 844910 * 2 ^ 59
def prefixEnd_844910 : Nat := 4983230072969 + 3 ^ 40 * 844910 * 2
def baseEnd_844910 : Nat := 96409986620087670986519

theorem tailTrace_844910 : CollatzResearch.WordTrace tailWord_844910 prefixEnd_844910 96409986620087670986519 := by
  unfold tailWord_844910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3852049921130355498108523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20544266246028562656578789 3852049921130355498108523)
  ·
    refine ⟨5778074881695533247162785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3852049921130355498108523 5778074881695533247162785)
    ·
      refine ⟨4333556161271649935372089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5778074881695533247162785 4333556161271649935372089)
      ·
        refine ⟨3250167120953737451529067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4333556161271649935372089 3250167120953737451529067)
        ·
          refine ⟨4875250681430606177293601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3250167120953737451529067 4875250681430606177293601)
          ·
            refine ⟨3656438011072954632970201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4875250681430606177293601 3656438011072954632970201)
            ·
              refine ⟨2742328508304715974727651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3656438011072954632970201 2742328508304715974727651)
              ·
                refine ⟨4113492762457073962091477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2742328508304715974727651 4113492762457073962091477)
                ·
                  refine ⟨96409986620087670986519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4113492762457073962091477 96409986620087670986519)
                  ·
                    rfl

theorem cell22_844910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_844910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_844910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_844910 prefixEnd_844910 := by exact prefixLift 844910
  have htrace : WordTrace (prefixWord ++ tailWord_844910) baseStart_844910 baseEnd_844910 := by
    simpa [prefixWord, tailWord_844910, baseEnd_844910] using wordTrace_append hprefix tailTrace_844910
  have hstable : (prefixWord ++ tailWord_844910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844910).length < 2 ^ (prefixWord ++ tailWord_844910).sum := by decide
  have hdescent : baseEnd_844910 < baseStart_844910 := by decide
  rcases family_descends (prefixWord ++ tailWord_844910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845002 : List Nat := [3, 1, 2, 1, 3, 2, 3, 1, 2, 4]
def baseStart_845002 : Nat := 118140960795 + 845002 * 2 ^ 59
def prefixEnd_845002 : Nat := 4983230072969 + 3 ^ 40 * 845002 * 2
def baseEnd_845002 : Nat := 289261453340405439659275

theorem tailTrace_845002 : CollatzResearch.WordTrace tailWord_845002 prefixEnd_845002 289261453340405439659275 := by
  unfold tailWord_845002
  simp only [CollatzResearch.WordTrace]
  refine ⟨7704938721177385924304315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20546503256473029131478173 7704938721177385924304315)
  ·
    refine ⟨11557408081766078886456473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7704938721177385924304315 11557408081766078886456473)
    ·
      refine ⟨8668056061324559164842355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11557408081766078886456473 8668056061324559164842355)
      ·
        refine ⟨13002084091986838747263533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8668056061324559164842355 13002084091986838747263533)
        ·
          refine ⟨4875781534495064530223825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13002084091986838747263533 4875781534495064530223825)
          ·
            refine ⟨3656836150871298397667869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4875781534495064530223825 3656836150871298397667869)
            ·
              refine ⟨1371313556576736899125451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3656836150871298397667869 1371313556576736899125451)
              ·
                refine ⟨2056970334865105348688177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371313556576736899125451 2056970334865105348688177)
                ·
                  refine ⟨1542727751148829011516133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2056970334865105348688177 1542727751148829011516133)
                  ·
                    refine ⟨289261453340405439659275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1542727751148829011516133 289261453340405439659275)
                    ·
                      rfl

theorem cell22_845002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_845002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845002 prefixEnd_845002 := by exact prefixLift 845002
  have htrace : WordTrace (prefixWord ++ tailWord_845002) baseStart_845002 baseEnd_845002 := by
    simpa [prefixWord, tailWord_845002, baseEnd_845002] using wordTrace_append hprefix tailTrace_845002
  have hstable : (prefixWord ++ tailWord_845002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845002).length < 2 ^ (prefixWord ++ tailWord_845002).sum := by decide
  have hdescent : baseEnd_845002 < baseStart_845002 := by decide
  rcases family_descends (prefixWord ++ tailWord_845002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845075 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 7, 4]
def baseStart_845075 : Nat := 118140960795 + 845075 * 2 ^ 59
def prefixEnd_845075 : Nat := 4983230072969 + 3 ^ 40 * 845075 * 2
def baseEnd_845075 : Nat := 289286442732257582584051

theorem tailTrace_845075 : CollatzResearch.WordTrace tailWord_845075 prefixEnd_845075 289286442732257582584051 := by
  unfold tailWord_845075
  simp only [CollatzResearch.WordTrace]
  refine ⟨30822417413445077164624679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20548278275630051443083119 30822417413445077164624679)
  ·
    refine ⟨46233626120167615746937019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30822417413445077164624679 46233626120167615746937019)
    ·
      refine ⟨69350439180251423620405529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46233626120167615746937019 69350439180251423620405529)
      ·
        refine ⟨52012829385188567715304147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69350439180251423620405529 52012829385188567715304147)
        ·
          refine ⟨78019244077782851572956221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52012829385188567715304147 78019244077782851572956221)
          ·
            refine ⟨29257216529168569339858583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78019244077782851572956221 29257216529168569339858583)
            ·
              refine ⟨43885824793752854009787875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29257216529168569339858583 43885824793752854009787875)
              ·
                refine ⟨65828737190629281014681813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43885824793752854009787875 65828737190629281014681813)
                ·
                  refine ⟨1542861027905373773781605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 65828737190629281014681813 1542861027905373773781605)
                  ·
                    refine ⟨289286442732257582584051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1542861027905373773781605 289286442732257582584051)
                    ·
                      rfl

theorem cell22_845075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 4].length) (baseStart_845075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845075 prefixEnd_845075 := by exact prefixLift 845075
  have htrace : WordTrace (prefixWord ++ tailWord_845075) baseStart_845075 baseEnd_845075 := by
    simpa [prefixWord, tailWord_845075, baseEnd_845075] using wordTrace_append hprefix tailTrace_845075
  have hstable : (prefixWord ++ tailWord_845075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845075).length < 2 ^ (prefixWord ++ tailWord_845075).sum := by decide
  have hdescent : baseEnd_845075 < baseStart_845075 := by decide
  rcases family_descends (prefixWord ++ tailWord_845075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845092 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_845092 : Nat := 118140960795 + 845092 * 2 ^ 59
def prefixEnd_845092 : Nat := 4983230072969 + 3 ^ 40 * 845092 * 2
def baseEnd_845092 : Nat := 289292262179675204908999

theorem tailTrace_845092 : CollatzResearch.WordTrace tailWord_845092 prefixEnd_845092 289292262179675204908999 := by
  unfold tailWord_845092
  simp only [CollatzResearch.WordTrace]
  refine ⟨15411518727191744533996765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20548691636255659378662353 15411518727191744533996765)
  ·
    refine ⟨5779319522696904200248787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15411518727191744533996765 5779319522696904200248787)
    ·
      refine ⟨8668979284045356300373181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5779319522696904200248787 8668979284045356300373181)
      ·
        refine ⟨3250867231517008612639943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8668979284045356300373181 3250867231517008612639943)
        ·
          refine ⟨4876300847275512918959915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3250867231517008612639943 4876300847275512918959915)
          ·
            refine ⟨7314451270913269378439873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4876300847275512918959915 7314451270913269378439873)
            ·
              refine ⟨5485838453184952033829905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7314451270913269378439873 5485838453184952033829905)
              ·
                refine ⟨4114378839888714025372429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5485838453184952033829905 4114378839888714025372429)
                ·
                  refine ⟨1542892064958267759514661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4114378839888714025372429 1542892064958267759514661)
                  ·
                    refine ⟨289292262179675204908999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1542892064958267759514661 289292262179675204908999)
                    ·
                      rfl

theorem cell22_845092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_845092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845092 prefixEnd_845092 := by exact prefixLift 845092
  have htrace : WordTrace (prefixWord ++ tailWord_845092) baseStart_845092 baseEnd_845092 := by
    simpa [prefixWord, tailWord_845092, baseEnd_845092] using wordTrace_append hprefix tailTrace_845092
  have hstable : (prefixWord ++ tailWord_845092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845092).length < 2 ^ (prefixWord ++ tailWord_845092).sum := by decide
  have hdescent : baseEnd_845092 < baseStart_845092 := by decide
  rcases family_descends (prefixWord ++ tailWord_845092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845096 : List Nat := [2, 1, 5, 1, 2, 3, 2, 1, 5]
def baseStart_845096 : Nat := 118140960795 + 845096 * 2 ^ 59
def prefixEnd_845096 : Nat := 4983230072969 + 3 ^ 40 * 845096 * 2
def baseEnd_845096 : Nat := 96431210487140175936329

theorem tailTrace_845096 : CollatzResearch.WordTrace tailWord_845096 prefixEnd_845096 96431210487140175936329 := by
  unfold tailWord_845096
  simp only [CollatzResearch.WordTrace]
  refine ⟨15411591673184498875569571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20548788897579331834092761 15411591673184498875569571)
  ·
    refine ⟨23117387509776748313354357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15411591673184498875569571 23117387509776748313354357)
    ·
      refine ⟨2167255079041570154376971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23117387509776748313354357 2167255079041570154376971)
      ·
        refine ⟨3250882618562355231565457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2167255079041570154376971 3250882618562355231565457)
        ·
          refine ⟨2438161963921766423674093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3250882618562355231565457 2438161963921766423674093)
          ·
            refine ⟨914310736470662408877785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2438161963921766423674093 914310736470662408877785)
            ·
              refine ⟨685733052352996806658339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 914310736470662408877785 685733052352996806658339)
              ·
                refine ⟨1028599578529495209987509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685733052352996806658339 1028599578529495209987509)
                ·
                  refine ⟨96431210487140175936329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1028599578529495209987509 96431210487140175936329)
                  ·
                    rfl

theorem cell22_845096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 5].length) (baseStart_845096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845096 prefixEnd_845096 := by exact prefixLift 845096
  have htrace : WordTrace (prefixWord ++ tailWord_845096) baseStart_845096 baseEnd_845096 := by
    simpa [prefixWord, tailWord_845096, baseEnd_845096] using wordTrace_append hprefix tailTrace_845096
  have hstable : (prefixWord ++ tailWord_845096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845096).length < 2 ^ (prefixWord ++ tailWord_845096).sum := by decide
  have hdescent : baseEnd_845096 < baseStart_845096 := by decide
  rcases family_descends (prefixWord ++ tailWord_845096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845109 : List Nat := [1, 3, 3, 1, 2, 2, 3, 2, 1, 4]
def baseStart_845109 : Nat := 118140960795 + 845109 * 2 ^ 59
def prefixEnd_845109 : Nat := 4983230072969 + 3 ^ 40 * 845109 * 2
def baseEnd_845109 : Nat := 289298081627092827233947

theorem tailTrace_845109 : CollatzResearch.WordTrace tailWord_845109 prefixEnd_845109 289298081627092827233947 := by
  unfold tailWord_845109
  simp only [CollatzResearch.WordTrace]
  refine ⟨30823657495321900971362381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20549104996881267314241587 30823657495321900971362381)
  ·
    refine ⟨11558871560745712864260893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30823657495321900971362381 11558871560745712864260893)
    ·
      refine ⟨4334576835279642324097835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11558871560745712864260893 4334576835279642324097835)
      ·
        refine ⟨6501865252919463486146753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4334576835279642324097835 6501865252919463486146753)
        ·
          refine ⟨4876398939689597614610065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6501865252919463486146753 4876398939689597614610065)
          ·
            refine ⟨3657299204767198210957549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4876398939689597614610065 3657299204767198210957549)
            ·
              refine ⟨1371487201787699329109081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3657299204767198210957549 1371487201787699329109081)
              ·
                refine ⟨1028615401340774496831811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1371487201787699329109081 1028615401340774496831811)
                ·
                  refine ⟨1542923102011161745247717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028615401340774496831811 1542923102011161745247717)
                  ·
                    refine ⟨289298081627092827233947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1542923102011161745247717 289298081627092827233947)
                    ·
                      rfl

theorem cell22_845109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_845109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845109 prefixEnd_845109 := by exact prefixLift 845109
  have htrace : WordTrace (prefixWord ++ tailWord_845109) baseStart_845109 baseEnd_845109 := by
    simpa [prefixWord, tailWord_845109, baseEnd_845109] using wordTrace_append hprefix tailTrace_845109
  have hstable : (prefixWord ++ tailWord_845109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845109).length < 2 ^ (prefixWord ++ tailWord_845109).sum := by decide
  have hdescent : baseEnd_845109 < baseStart_845109 := by decide
  rcases family_descends (prefixWord ++ tailWord_845109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845137 : List Nat := [1, 2, 2, 1, 4, 1, 1, 4, 2, 4]
def baseStart_845137 : Nat := 118140960795 + 845137 * 2 ^ 59
def prefixEnd_845137 : Nat := 4983230072969 + 3 ^ 40 * 845137 * 2
def baseEnd_845137 : Nat := 289307666599310087533861

theorem tailTrace_845137 : CollatzResearch.WordTrace tailWord_845137 prefixEnd_845137 289307666599310087533861 := by
  unfold tailWord_845137
  simp only [CollatzResearch.WordTrace]
  refine ⟨30824678739220461753381665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20549785826146974502254443 30824678739220461753381665)
  ·
    refine ⟨23118509054415346315036249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30824678739220461753381665 23118509054415346315036249)
    ·
      refine ⟨17338881790811509736277187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23118509054415346315036249 17338881790811509736277187)
      ·
        refine ⟨26008322686217264604415781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17338881790811509736277187 26008322686217264604415781)
        ·
          refine ⟨4876560503665737113327959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26008322686217264604415781 4876560503665737113327959)
          ·
            refine ⟨7314840755498605669991939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4876560503665737113327959 7314840755498605669991939)
            ·
              refine ⟨10972261133247908504987909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7314840755498605669991939 10972261133247908504987909)
              ·
                refine ⟨2057298962483982844685233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10972261133247908504987909 2057298962483982844685233)
                ·
                  refine ⟨1542974221862987133513925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2057298962483982844685233 1542974221862987133513925)
                  ·
                    refine ⟨289307666599310087533861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1542974221862987133513925 289307666599310087533861)
                    ·
                      rfl

theorem cell22_845137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_845137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845137 prefixEnd_845137 := by exact prefixLift 845137
  have htrace : WordTrace (prefixWord ++ tailWord_845137) baseStart_845137 baseEnd_845137 := by
    simpa [prefixWord, tailWord_845137, baseEnd_845137] using wordTrace_append hprefix tailTrace_845137
  have hstable : (prefixWord ++ tailWord_845137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845137).length < 2 ^ (prefixWord ++ tailWord_845137).sum := by decide
  have hdescent : baseEnd_845137 < baseStart_845137 := by decide
  rcases family_descends (prefixWord ++ tailWord_845137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845139 : List Nat := [1, 1, 1, 2, 1, 1, 8, 2, 2, 3]
def baseStart_845139 : Nat := 118140960795 + 845139 * 2 ^ 59
def prefixEnd_845139 : Nat := 4983230072969 + 3 ^ 40 * 845139 * 2
def baseEnd_845139 : Nat := 289308351240182748983855

theorem tailTrace_845139 : CollatzResearch.WordTrace tailWord_845139 prefixEnd_845139 289308351240182748983855 := by
  unfold tailWord_845139
  simp only [CollatzResearch.WordTrace]
  refine ⟨30824751685213216094954471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20549834456808810729969647 30824751685213216094954471)
  ·
    refine ⟨46237127527819824142431707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30824751685213216094954471 46237127527819824142431707)
    ·
      refine ⟨69355691291729736213647561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46237127527819824142431707 69355691291729736213647561)
      ·
        refine ⟨52016768468797302160235671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69355691291729736213647561 52016768468797302160235671)
        ·
          refine ⟨78025152703195953240353507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52016768468797302160235671 78025152703195953240353507)
          ·
            refine ⟨117037729054793929860530261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78025152703195953240353507 117037729054793929860530261)
            ·
              refine ⟨1371535887360866365553089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 117037729054793929860530261 1371535887360866365553089)
              ·
                refine ⟨1028651915520649774164817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1371535887360866365553089 1028651915520649774164817)
                ·
                  refine ⟨771488936640487330623613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1028651915520649774164817 771488936640487330623613)
                  ·
                    refine ⟨289308351240182748983855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 771488936640487330623613 289308351240182748983855)
                    ·
                      rfl

theorem cell22_845139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 3].length) (baseStart_845139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845139 prefixEnd_845139 := by exact prefixLift 845139
  have htrace : WordTrace (prefixWord ++ tailWord_845139) baseStart_845139 baseEnd_845139 := by
    simpa [prefixWord, tailWord_845139, baseEnd_845139] using wordTrace_append hprefix tailTrace_845139
  have hstable : (prefixWord ++ tailWord_845139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845139).length < 2 ^ (prefixWord ++ tailWord_845139).sum := by decide
  have hdescent : baseEnd_845139 < baseStart_845139 := by decide
  rcases family_descends (prefixWord ++ tailWord_845139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845141 : List Nat := [1, 3, 2, 2, 3, 1, 4, 2, 4]
def baseStart_845141 : Nat := 118140960795 + 845141 * 2 ^ 59
def prefixEnd_845141 : Nat := 4983230072969 + 3 ^ 40 * 845141 * 2
def baseEnd_845141 : Nat := 96436345293685136811283

theorem tailTrace_845141 : CollatzResearch.WordTrace tailWord_845141 prefixEnd_845141 96436345293685136811283 := by
  unfold tailWord_845141
  simp only [CollatzResearch.WordTrace]
  refine ⟨30824824631205970436527277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20549883087470646957684851 30824824631205970436527277)
  ·
    refine ⟨11559309236702238913697729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30824824631205970436527277 11559309236702238913697729)
    ·
      refine ⟨8669481927526679185273297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11559309236702238913697729 8669481927526679185273297)
      ·
        refine ⟨6502111445645009388954973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8669481927526679185273297 6502111445645009388954973)
        ·
          refine ⟨2438291792116878520858115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6502111445645009388954973 2438291792116878520858115)
          ·
            refine ⟨3657437688175317781287173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2438291792116878520858115 3657437688175317781287173)
            ·
              refine ⟨685769566532872083991345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3657437688175317781287173 685769566532872083991345)
              ·
                refine ⟨514327174899654062993509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 685769566532872083991345 514327174899654062993509)
                ·
                  refine ⟨96436345293685136811283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 514327174899654062993509 96436345293685136811283)
                  ·
                    rfl

theorem cell22_845141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_845141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845141 prefixEnd_845141 := by exact prefixLift 845141
  have htrace : WordTrace (prefixWord ++ tailWord_845141) baseStart_845141 baseEnd_845141 := by
    simpa [prefixWord, tailWord_845141, baseEnd_845141] using wordTrace_append hprefix tailTrace_845141
  have hstable : (prefixWord ++ tailWord_845141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845141).length < 2 ^ (prefixWord ++ tailWord_845141).sum := by decide
  have hdescent : baseEnd_845141 < baseStart_845141 := by decide
  rcases family_descends (prefixWord ++ tailWord_845141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845152 : List Nat := [2, 1, 1, 3, 4, 1, 3, 7]
def baseStart_845152 : Nat := 118140960795 + 845152 * 2 ^ 59
def prefixEnd_845152 : Nat := 4983230072969 + 3 ^ 40 * 845152 * 2
def baseEnd_845152 : Nat := 32145866822872783156535

theorem tailTrace_845152 : CollatzResearch.WordTrace tailWord_845152 prefixEnd_845152 32145866822872783156535 := by
  unfold tailWord_845152
  simp only [CollatzResearch.WordTrace]
  refine ⟨15412612917083059657588855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20550150556110746210118473 15412612917083059657588855)
  ·
    refine ⟨23118919375624589486383283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15412612917083059657588855 23118919375624589486383283)
    ·
      refine ⟨34678379063436884229574925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23118919375624589486383283 34678379063436884229574925)
      ·
        refine ⟨13004392148788831586090597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34678379063436884229574925 13004392148788831586090597)
        ·
          refine ⟨2438323527897905922391987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13004392148788831586090597 2438323527897905922391987)
          ·
            refine ⟨3657485291846858883587981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2438323527897905922391987 3657485291846858883587981)
            ·
              refine ⟨1371556984442572081345493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3657485291846858883587981 1371556984442572081345493)
              ·
                refine ⟨32145866822872783156535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1371556984442572081345493 32145866822872783156535)
                ·
                  rfl

theorem cell22_845152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 7].length) (baseStart_845152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845152 prefixEnd_845152 := by exact prefixLift 845152
  have htrace : WordTrace (prefixWord ++ tailWord_845152) baseStart_845152 baseEnd_845152 := by
    simpa [prefixWord, tailWord_845152, baseEnd_845152] using wordTrace_append hprefix tailTrace_845152
  have hstable : (prefixWord ++ tailWord_845152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845152).length < 2 ^ (prefixWord ++ tailWord_845152).sum := by decide
  have hdescent : baseEnd_845152 < baseStart_845152 := by decide
  rcases family_descends (prefixWord ++ tailWord_845152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845259 : List Nat := [1, 1, 1, 1, 3, 3, 2, 6, 4]
def baseStart_845259 : Nat := 118140960795 + 845259 * 2 ^ 59
def prefixEnd_845259 : Nat := 4983230072969 + 3 ^ 40 * 845259 * 2
def baseEnd_845259 : Nat := 96449809897514145327829

theorem tailTrace_845259 : CollatzResearch.WordTrace tailWord_845259 prefixEnd_845259 96449809897514145327829 := by
  unfold tailWord_845259
  simp only [CollatzResearch.WordTrace]
  refine ⟨30829128444778476589322831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20552752296518984392881887 30829128444778476589322831)
  ·
    refine ⟨46243692667167714883984247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30829128444778476589322831 46243692667167714883984247)
    ·
      refine ⟨69365539000751572325976371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46243692667167714883984247 69365539000751572325976371)
      ·
        refine ⟨104048308501127358488964557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69365539000751572325976371 104048308501127358488964557)
        ·
          refine ⟨39018115687922759433361709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104048308501127358488964557 39018115687922759433361709)
          ·
            refine ⟨14631793382971034787510641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39018115687922759433361709 14631793382971034787510641)
            ·
              refine ⟨10973845037228276090632981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14631793382971034787510641 10973845037228276090632981)
              ·
                refine ⟨514398986120075441748421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10973845037228276090632981 514398986120075441748421)
                ·
                  refine ⟨96449809897514145327829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 514398986120075441748421 96449809897514145327829)
                  ·
                    rfl

theorem cell22_845259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 4].length) (baseStart_845259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845259 prefixEnd_845259 := by exact prefixLift 845259
  have htrace : WordTrace (prefixWord ++ tailWord_845259) baseStart_845259 baseEnd_845259 := by
    simpa [prefixWord, tailWord_845259, baseEnd_845259] using wordTrace_append hprefix tailTrace_845259
  have hstable : (prefixWord ++ tailWord_845259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845259).length < 2 ^ (prefixWord ++ tailWord_845259).sum := by decide
  have hdescent : baseEnd_845259 < baseStart_845259 := by decide
  rcases family_descends (prefixWord ++ tailWord_845259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845272 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 3, 6]
def baseStart_845272 : Nat := 118140960795 + 845272 * 2 ^ 59
def prefixEnd_845272 : Nat := 4983230072969 + 3 ^ 40 * 845272 * 2
def baseEnd_845272 : Nat := 289353879858214735408447

theorem tailTrace_845272 : CollatzResearch.WordTrace tailWord_845272 prefixEnd_845272 289353879858214735408447 := by
  unfold tailWord_845272
  simp only [CollatzResearch.WordTrace]
  refine ⟨15414801296865689904773035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20553068395820919873030713 15414801296865689904773035)
  ·
    refine ⟨23122201945298534857159553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15414801296865689904773035 23122201945298534857159553)
    ·
      refine ⟨17341651458973901142869665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23122201945298534857159553 17341651458973901142869665)
      ·
        refine ⟨13006238594230425857152249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17341651458973901142869665 13006238594230425857152249)
        ·
          refine ⟨9754678945672819392864187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13006238594230425857152249 9754678945672819392864187)
          ·
            refine ⟨14632018418509229089296281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9754678945672819392864187 14632018418509229089296281)
            ·
              refine ⟨10974013813881921816972211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14632018418509229089296281 10974013813881921816972211)
              ·
                refine ⟨16461020720822882725458317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10974013813881921816972211 16461020720822882725458317)
                ·
                  refine ⟨6172882770308581022046869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16461020720822882725458317 6172882770308581022046869)
                  ·
                    refine ⟨289353879858214735408447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6172882770308581022046869 289353879858214735408447)
                    ·
                      rfl

theorem cell22_845272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_845272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845272 prefixEnd_845272 := by exact prefixLift 845272
  have htrace : WordTrace (prefixWord ++ tailWord_845272) baseStart_845272 baseEnd_845272 := by
    simpa [prefixWord, tailWord_845272, baseEnd_845272] using wordTrace_append hprefix tailTrace_845272
  have hstable : (prefixWord ++ tailWord_845272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845272).length < 2 ^ (prefixWord ++ tailWord_845272).sum := by decide
  have hdescent : baseEnd_845272 < baseStart_845272 := by decide
  rcases family_descends (prefixWord ++ tailWord_845272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845310 : List Nat := [4, 2, 2, 3, 1, 1, 1, 4, 4]
def baseStart_845310 : Nat := 118140960795 + 845310 * 2 ^ 59
def prefixEnd_845310 : Nat := 4983230072969 + 3 ^ 40 * 845310 * 2
def baseEnd_845310 : Nat := 96455629344931767652777

theorem tailTrace_845310 : CollatzResearch.WordTrace tailWord_845310 prefixEnd_845310 96455629344931767652777 := by
  unfold tailWord_845310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3853873570949214037428673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20553992378395808199619589 3853873570949214037428673)
  ·
    refine ⟨2890405178211910528071505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3853873570949214037428673 2890405178211910528071505)
    ·
      refine ⟨2167803883658932896053629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2890405178211910528071505 2167803883658932896053629)
      ·
        refine ⟨812926456372099836020111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2167803883658932896053629 812926456372099836020111)
        ·
          refine ⟨1219389684558149754030167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812926456372099836020111 1219389684558149754030167)
          ·
            refine ⟨1829084526837224631045251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219389684558149754030167 1829084526837224631045251)
            ·
              refine ⟨2743626790255836946567877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829084526837224631045251 2743626790255836946567877)
              ·
                refine ⟨514430023172969427481477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2743626790255836946567877 514430023172969427481477)
                ·
                  refine ⟨96455629344931767652777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 514430023172969427481477 96455629344931767652777)
                  ·
                    rfl

theorem cell22_845310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_845310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845310 prefixEnd_845310 := by exact prefixLift 845310
  have htrace : WordTrace (prefixWord ++ tailWord_845310) baseStart_845310 baseEnd_845310 := by
    simpa [prefixWord, tailWord_845310, baseEnd_845310] using wordTrace_append hprefix tailTrace_845310
  have hstable : (prefixWord ++ tailWord_845310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845310).length < 2 ^ (prefixWord ++ tailWord_845310).sum := by decide
  have hdescent : baseEnd_845310 < baseStart_845310 := by decide
  rcases family_descends (prefixWord ++ tailWord_845310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845325 : List Nat := [1, 7, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_845325 : Nat := 118140960795 + 845325 * 2 ^ 59
def prefixEnd_845325 : Nat := 4983230072969 + 3 ^ 40 * 845325 * 2
def baseEnd_845325 : Nat := 289372022841340263833285

theorem tailTrace_845325 : CollatzResearch.WordTrace tailWord_845325 prefixEnd_845325 289372022841340263833285 := by
  unfold tailWord_845325
  simp only [CollatzResearch.WordTrace]
  refine ⟨30831535662539369861225429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20554357108359579907483619 30831535662539369861225429)
  ·
    refine ⟨722614117090766481122471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 30831535662539369861225429 722614117090766481122471)
    ·
      refine ⟨1083921175636149721683707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 722614117090766481122471 1083921175636149721683707)
      ·
        refine ⟨1625881763454224582525561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1083921175636149721683707 1625881763454224582525561)
        ·
          refine ⟨1219411322590668436894171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1625881763454224582525561 1219411322590668436894171)
          ·
            refine ⟨1829116983886002655341257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219411322590668436894171 1829116983886002655341257)
            ·
              refine ⟨1371837737914501991505943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1829116983886002655341257 1371837737914501991505943)
              ·
                refine ⟨2057756606871752987258915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371837737914501991505943 2057756606871752987258915)
                ·
                  refine ⟨3086634910307629480888373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2057756606871752987258915 3086634910307629480888373)
                  ·
                    refine ⟨289372022841340263833285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3086634910307629480888373 289372022841340263833285)
                    ·
                      rfl

theorem cell22_845325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_845325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845325 prefixEnd_845325 := by exact prefixLift 845325
  have htrace : WordTrace (prefixWord ++ tailWord_845325) baseStart_845325 baseEnd_845325 := by
    simpa [prefixWord, tailWord_845325, baseEnd_845325] using wordTrace_append hprefix tailTrace_845325
  have hstable : (prefixWord ++ tailWord_845325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845325).length < 2 ^ (prefixWord ++ tailWord_845325).sum := by decide
  have hdescent : baseEnd_845325 < baseStart_845325 := by decide
  rcases family_descends (prefixWord ++ tailWord_845325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845383 : List Nat := [1, 1, 4, 1, 5, 1, 3, 1, 5]
def baseStart_845383 : Nat := 118140960795 + 845383 * 2 ^ 59
def prefixEnd_845383 : Nat := 4983230072969 + 3 ^ 40 * 845383 * 2
def baseEnd_845383 : Nat := 96463959142215815294369

theorem tailTrace_845383 : CollatzResearch.WordTrace tailWord_845383 prefixEnd_845383 96463959142215815294369 := by
  unfold tailWord_845383
  simp only [CollatzResearch.WordTrace]
  refine ⟨30833651096329245766836803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20555767397552830511224535 30833651096329245766836803)
  ·
    refine ⟨46250476644493868650255205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30833651096329245766836803 46250476644493868650255205)
    ·
      refine ⟨8671964370842600371922851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46250476644493868650255205 8671964370842600371922851)
      ·
        refine ⟨13007946556263900557884277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8671964370842600371922851 13007946556263900557884277)
        ·
          refine ⟨1219494989649740677301651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13007946556263900557884277 1219494989649740677301651)
          ·
            refine ⟨1829242484474611015952477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219494989649740677301651 1829242484474611015952477)
            ·
              refine ⟨685965931677979130982179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1829242484474611015952477 685965931677979130982179)
              ·
                refine ⟨1028948897516968696473269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685965931677979130982179 1028948897516968696473269)
                ·
                  refine ⟨96463959142215815294369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1028948897516968696473269 96463959142215815294369)
                  ·
                    rfl

theorem cell22_845383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 5].length) (baseStart_845383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845383 prefixEnd_845383 := by exact prefixLift 845383
  have htrace : WordTrace (prefixWord ++ tailWord_845383) baseStart_845383 baseEnd_845383 := by
    simpa [prefixWord, tailWord_845383, baseEnd_845383] using wordTrace_append hprefix tailTrace_845383
  have hstable : (prefixWord ++ tailWord_845383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845383).length < 2 ^ (prefixWord ++ tailWord_845383).sum := by decide
  have hdescent : baseEnd_845383 < baseStart_845383 := by decide
  rcases family_descends (prefixWord ++ tailWord_845383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845409 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 3, 5]
def baseStart_845409 : Nat := 118140960795 + 845409 * 2 ^ 59
def prefixEnd_845409 : Nat := 4983230072969 + 3 ^ 40 * 845409 * 2
def baseEnd_845409 : Nat := 289400777757992044733027

theorem tailTrace_845409 : CollatzResearch.WordTrace tailWord_845409 prefixEnd_845409 289400777757992044733027 := by
  unfold tailWord_845409
  simp only [CollatzResearch.WordTrace]
  refine ⟨30834599394235052207283281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20556399596156701471522187 30834599394235052207283281)
  ·
    refine ⟨23125949545676289155462461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30834599394235052207283281 23125949545676289155462461)
    ·
      refine ⟨8672231079628608433298423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23125949545676289155462461 8672231079628608433298423)
      ·
        refine ⟨13008346619442912649947635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8672231079628608433298423 13008346619442912649947635)
        ·
          refine ⟨19512519929164368974921453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13008346619442912649947635 19512519929164368974921453)
          ·
            refine ⟨7317194973436638365595545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19512519929164368974921453 7317194973436638365595545)
            ·
              refine ⟨5487896230077478774196659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7317194973436638365595545 5487896230077478774196659)
              ·
                refine ⟨8231844345116218161294989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5487896230077478774196659 8231844345116218161294989)
                ·
                  refine ⟨3086941629418581810485621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8231844345116218161294989 3086941629418581810485621)
                  ·
                    refine ⟨289400777757992044733027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3086941629418581810485621 289400777757992044733027)
                    ·
                      rfl

theorem cell22_845409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_845409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845409 prefixEnd_845409 := by exact prefixLift 845409
  have htrace : WordTrace (prefixWord ++ tailWord_845409) baseStart_845409 baseEnd_845409 := by
    simpa [prefixWord, tailWord_845409, baseEnd_845409] using wordTrace_append hprefix tailTrace_845409
  have hstable : (prefixWord ++ tailWord_845409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845409).length < 2 ^ (prefixWord ++ tailWord_845409).sum := by decide
  have hdescent : baseEnd_845409 < baseStart_845409 := by decide
  rcases family_descends (prefixWord ++ tailWord_845409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845501 : List Nat := [1, 4, 1, 2, 1, 2, 1, 5, 5]
def baseStart_845501 : Nat := 118140960795 + 845501 * 2 ^ 59
def prefixEnd_845501 : Nat := 4983230072969 + 3 ^ 40 * 845501 * 2
def baseEnd_845501 : Nat := 96477423746044823810915

theorem tailTrace_845501 : CollatzResearch.WordTrace tailWord_845501 prefixEnd_845501 96477423746044823810915 := by
  unfold tailWord_845501
  simp only [CollatzResearch.WordTrace]
  refine ⟨30837954909901751919632357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20558636606601167946421571 30837954909901751919632357)
  ·
    refine ⟨5782116545606578484931067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30837954909901751919632357 5782116545606578484931067)
    ·
      refine ⟨8673174818409867727396601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5782116545606578484931067 8673174818409867727396601)
      ·
        refine ⟨6504881113807400795547451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8673174818409867727396601 6504881113807400795547451)
        ·
          refine ⟨9757321670711101193321177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6504881113807400795547451 9757321670711101193321177)
          ·
            refine ⟨7317991253033325894990883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9757321670711101193321177 7317991253033325894990883)
            ·
              refine ⟨10976986879549988842486325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7317991253033325894990883 10976986879549988842486325)
              ·
                refine ⟨1029092519957811453983093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10976986879549988842486325 1029092519957811453983093)
                ·
                  refine ⟨96477423746044823810915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1029092519957811453983093 96477423746044823810915)
                  ·
                    rfl

theorem cell22_845501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_845501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845501 prefixEnd_845501 := by exact prefixLift 845501
  have htrace : WordTrace (prefixWord ++ tailWord_845501) baseStart_845501 baseEnd_845501 := by
    simpa [prefixWord, tailWord_845501, baseEnd_845501] using wordTrace_append hprefix tailTrace_845501
  have hstable : (prefixWord ++ tailWord_845501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845501).length < 2 ^ (prefixWord ++ tailWord_845501).sum := by decide
  have hdescent : baseEnd_845501 < baseStart_845501 := by decide
  rcases family_descends (prefixWord ++ tailWord_845501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845522 : List Nat := [3, 2, 2, 2, 2, 2, 2, 3, 1, 3]
def baseStart_845522 : Nat := 118140960795 + 845522 * 2 ^ 59
def prefixEnd_845522 : Nat := 4983230072969 + 3 ^ 40 * 845522 * 2
def baseEnd_845522 : Nat := 289439459967297416657681

theorem tailTrace_845522 : CollatzResearch.WordTrace tailWord_845522 prefixEnd_845522 289439459967297416657681 := by
  unfold tailWord_845522
  simp only [CollatzResearch.WordTrace]
  refine ⟨7709680210706418126536705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20559147228550448337431213 7709680210706418126536705)
  ·
    refine ⟨5782260158029813594902529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7709680210706418126536705 5782260158029813594902529)
    ·
      refine ⟨4336695118522360196176897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5782260158029813594902529 4336695118522360196176897)
      ·
        refine ⟨3252521338891770147132673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4336695118522360196176897 3252521338891770147132673)
        ·
          refine ⟨2439391004168827610349505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3252521338891770147132673 2439391004168827610349505)
          ·
            refine ⟨1829543253126620707762129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2439391004168827610349505 1829543253126620707762129)
            ·
              refine ⟨1372157439844965530821597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1829543253126620707762129 1372157439844965530821597)
              ·
                refine ⟨514559039941862074058099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1372157439844965530821597 514559039941862074058099)
                ·
                  refine ⟨771838559912793111087149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 514559039941862074058099 771838559912793111087149)
                  ·
                    refine ⟨289439459967297416657681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 771838559912793111087149 289439459967297416657681)
                    ·
                      rfl

theorem cell22_845522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_845522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845522 prefixEnd_845522 := by exact prefixLift 845522
  have htrace : WordTrace (prefixWord ++ tailWord_845522) baseStart_845522 baseEnd_845522 := by
    simpa [prefixWord, tailWord_845522, baseEnd_845522] using wordTrace_append hprefix tailTrace_845522
  have hstable : (prefixWord ++ tailWord_845522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845522).length < 2 ^ (prefixWord ++ tailWord_845522).sum := by decide
  have hdescent : baseEnd_845522 < baseStart_845522 := by decide
  rcases family_descends (prefixWord ++ tailWord_845522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845546 : List Nat := [3, 1, 3, 1, 1, 1, 3, 3, 6]
def baseStart_845546 : Nat := 118140960795 + 845546 * 2 ^ 59
def prefixEnd_845546 : Nat := 4983230072969 + 3 ^ 40 * 845546 * 2
def baseEnd_845546 : Nat := 96482558552589784685869

theorem tailTrace_845546 : CollatzResearch.WordTrace tailWord_845546 prefixEnd_845546 96482558552589784685869 := by
  unfold tailWord_845546
  simp only [CollatzResearch.WordTrace]
  refine ⟨7709899048684681151255123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20559730796492483070013661 7709899048684681151255123)
  ·
    refine ⟨11564848573027021726882685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7709899048684681151255123 11564848573027021726882685)
    ·
      refine ⟨4336818214885133147581007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11564848573027021726882685 4336818214885133147581007)
      ·
        refine ⟨6505227322327699721371511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4336818214885133147581007 6505227322327699721371511)
        ·
          refine ⟨9757840983491549582057267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6505227322327699721371511 9757840983491549582057267)
          ·
            refine ⟨14636761475237324373085901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9757840983491549582057267 14636761475237324373085901)
            ·
              refine ⟨5488785553213996639907213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14636761475237324373085901 5488785553213996639907213)
              ·
                refine ⟨2058294582455248739965205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5488785553213996639907213 2058294582455248739965205)
                ·
                  refine ⟨96482558552589784685869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2058294582455248739965205 96482558552589784685869)
                  ·
                    rfl

theorem cell22_845546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_845546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845546 prefixEnd_845546 := by exact prefixLift 845546
  have htrace : WordTrace (prefixWord ++ tailWord_845546) baseStart_845546 baseEnd_845546 := by
    simpa [prefixWord, tailWord_845546, baseEnd_845546] using wordTrace_append hprefix tailTrace_845546
  have hstable : (prefixWord ++ tailWord_845546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845546).length < 2 ^ (prefixWord ++ tailWord_845546).sum := by decide
  have hdescent : baseEnd_845546 < baseStart_845546 := by decide
  rcases family_descends (prefixWord ++ tailWord_845546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845576 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 1, 6]
def baseStart_845576 : Nat := 118140960795 + 845576 * 2 ^ 59
def prefixEnd_845576 : Nat := 4983230072969 + 3 ^ 40 * 845576 * 2
def baseEnd_845576 : Nat := 289457945270859275807515

theorem tailTrace_845576 : CollatzResearch.WordTrace tailWord_845576 prefixEnd_845576 289457945270859275807515 := by
  unfold tailWord_845576
  simp only [CollatzResearch.WordTrace]
  refine ⟨15420345192315019864306291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20560460256420026485741721 15420345192315019864306291)
  ·
    refine ⟨23130517788472529796459437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15420345192315019864306291 23130517788472529796459437)
    ·
      refine ⟨8673944170677198673672289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23130517788472529796459437 8673944170677198673672289)
      ·
        refine ⟨6505458128007899005254217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8673944170677198673672289 6505458128007899005254217)
        ·
          refine ⟨4879093596005924253940663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6505458128007899005254217 4879093596005924253940663)
          ·
            refine ⟨7318640394008886380910995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4879093596005924253940663 7318640394008886380910995)
            ·
              refine ⟨10977960591013329571366493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7318640394008886380910995 10977960591013329571366493)
              ·
                refine ⟨4116735221629998589262435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10977960591013329571366493 4116735221629998589262435)
                ·
                  refine ⟨6175102832444997883893653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4116735221629998589262435 6175102832444997883893653)
                  ·
                    refine ⟨289457945270859275807515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6175102832444997883893653 289457945270859275807515)
                    ·
                      rfl

theorem cell22_845576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_845576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845576 prefixEnd_845576 := by exact prefixLift 845576
  have htrace : WordTrace (prefixWord ++ tailWord_845576) baseStart_845576 baseEnd_845576 := by
    simpa [prefixWord, tailWord_845576, baseEnd_845576] using wordTrace_append hprefix tailTrace_845576
  have hstable : (prefixWord ++ tailWord_845576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845576).length < 2 ^ (prefixWord ++ tailWord_845576).sum := by decide
  have hdescent : baseEnd_845576 < baseStart_845576 := by decide
  rcases family_descends (prefixWord ++ tailWord_845576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845578 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 4, 3]
def baseStart_845578 : Nat := 118140960795 + 845578 * 2 ^ 59
def prefixEnd_845578 : Nat := 4983230072969 + 3 ^ 40 * 845578 * 2
def baseEnd_845578 : Nat := 289458629911731937257509

theorem tailTrace_845578 : CollatzResearch.WordTrace tailWord_845578 prefixEnd_845578 289458629911731937257509 := by
  unfold tailWord_845578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7710190832655698517546347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20560508887081862713456925 7710190832655698517546347)
  ·
    refine ⟨11565286248983547776319521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7710190832655698517546347 11565286248983547776319521)
    ·
      refine ⟨8673964686737660832239641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11565286248983547776319521 8673964686737660832239641)
      ·
        refine ⟨6505473515053245624179731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8673964686737660832239641 6505473515053245624179731)
        ·
          refine ⟨9758210272579868436269597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6505473515053245624179731 9758210272579868436269597)
          ·
            refine ⟨3659328852217450663601099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9758210272579868436269597 3659328852217450663601099)
            ·
              refine ⟨5488993278326175995401649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3659328852217450663601099 5488993278326175995401649)
              ·
                refine ⟨4116744958744631996551237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5488993278326175995401649 4116744958744631996551237)
                ·
                  refine ⟨771889679764618499353357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4116744958744631996551237 771889679764618499353357)
                  ·
                    refine ⟨289458629911731937257509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 771889679764618499353357 289458629911731937257509)
                    ·
                      rfl

theorem cell22_845578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_845578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845578 prefixEnd_845578 := by exact prefixLift 845578
  have htrace : WordTrace (prefixWord ++ tailWord_845578) baseStart_845578 baseEnd_845578 := by
    simpa [prefixWord, tailWord_845578, baseEnd_845578] using wordTrace_append hprefix tailTrace_845578
  have hstable : (prefixWord ++ tailWord_845578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845578).length < 2 ^ (prefixWord ++ tailWord_845578).sum := by decide
  have hdescent : baseEnd_845578 < baseStart_845578 := by decide
  rcases family_descends (prefixWord ++ tailWord_845578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845591 : List Nat := [1, 1, 3, 4, 2, 1, 10]
def baseStart_845591 : Nat := 118140960795 + 845591 * 2 ^ 59
def prefixEnd_845591 : Nat := 4983230072969 + 3 ^ 40 * 845591 * 2
def baseEnd_845591 : Nat := 10720854817681638395647

theorem tailTrace_845591 : CollatzResearch.WordTrace tailWord_845591 prefixEnd_845591 10720854817681638395647 := by
  unfold tailWord_845591
  simp only [CollatzResearch.WordTrace]
  refine ⟨30841237479575697290408627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20560824986383798193605751 30841237479575697290408627)
  ·
    refine ⟨46261856219363545935612941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30841237479575697290408627 46261856219363545935612941)
    ·
      refine ⟨17348196082261329725854853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46261856219363545935612941 17348196082261329725854853)
      ·
        refine ⟨3252786765423999323597785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17348196082261329725854853 3252786765423999323597785)
        ·
          refine ⟨2439590074067999492698339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3252786765423999323597785 2439590074067999492698339)
          ·
            refine ⟨3659385111101999239047509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2439590074067999492698339 3659385111101999239047509)
            ·
              refine ⟨10720854817681638395647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3659385111101999239047509 10720854817681638395647)
              ·
                rfl

theorem cell22_845591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 10].length) (baseStart_845591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845591 prefixEnd_845591 := by exact prefixLift 845591
  have htrace : WordTrace (prefixWord ++ tailWord_845591) baseStart_845591 baseEnd_845591 := by
    simpa [prefixWord, tailWord_845591, baseEnd_845591] using wordTrace_append hprefix tailTrace_845591
  have hstable : (prefixWord ++ tailWord_845591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845591).length < 2 ^ (prefixWord ++ tailWord_845591).sum := by decide
  have hdescent : baseEnd_845591 < baseStart_845591 := by decide
  rcases family_descends (prefixWord ++ tailWord_845591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845608 : List Nat := [2, 1, 5, 1, 1, 3, 2, 7]
def baseStart_845608 : Nat := 118140960795 + 845608 * 2 ^ 59
def prefixEnd_845608 : Nat := 4983230072969 + 3 ^ 40 * 845608 * 2
def baseEnd_845608 : Nat := 32163211058313539889713

theorem tailTrace_845608 : CollatzResearch.WordTrace tailWord_845608 prefixEnd_845608 32163211058313539889713 := by
  unfold tailWord_845608
  simp only [CollatzResearch.WordTrace]
  refine ⟨15420928760257054596888739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20561238347009406129184985 15420928760257054596888739)
  ·
    refine ⟨23131393140385581895333109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15420928760257054596888739 23131393140385581895333109)
    ·
      refine ⟨2168568106911148302687479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23131393140385581895333109 2168568106911148302687479)
      ·
        refine ⟨3252852160366722454031219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2168568106911148302687479 3252852160366722454031219)
        ·
          refine ⟨4879278240550083681046829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3252852160366722454031219 4879278240550083681046829)
          ·
            refine ⟨1829729340206281380392561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4879278240550083681046829 1829729340206281380392561)
            ·
              refine ⟨1372297005154711035294421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1829729340206281380392561 1372297005154711035294421)
              ·
                refine ⟨32163211058313539889713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1372297005154711035294421 32163211058313539889713)
                ·
                  rfl

theorem cell22_845608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 7].length) (baseStart_845608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845608 prefixEnd_845608 := by exact prefixLift 845608
  have htrace : WordTrace (prefixWord ++ tailWord_845608) baseStart_845608 baseEnd_845608 := by
    simpa [prefixWord, tailWord_845608, baseEnd_845608] using wordTrace_append hprefix tailTrace_845608
  have hstable : (prefixWord ++ tailWord_845608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845608).length < 2 ^ (prefixWord ++ tailWord_845608).sum := by decide
  have hdescent : baseEnd_845608 < baseStart_845608 := by decide
  rcases family_descends (prefixWord ++ tailWord_845608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845612 : List Nat := [2, 2, 1, 1, 1, 7, 2, 1, 2, 3]
def baseStart_845612 : Nat := 118140960795 + 845612 * 2 ^ 59
def prefixEnd_845612 : Nat := 4983230072969 + 3 ^ 40 * 845612 * 2
def baseEnd_845612 : Nat := 289470268806567181907405

theorem tailTrace_845612 : CollatzResearch.WordTrace tailWord_845612 prefixEnd_845612 289470268806567181907405 := by
  unfold tailWord_845612
  simp only [CollatzResearch.WordTrace]
  refine ⟨15421001706249808938461545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20561335608333078584615393 15421001706249808938461545)
  ·
    refine ⟨11565751279687356703846159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15421001706249808938461545 11565751279687356703846159)
    ·
      refine ⟨17348626919531035055769239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11565751279687356703846159 17348626919531035055769239)
      ·
        refine ⟨26022940379296552583653859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17348626919531035055769239 26022940379296552583653859)
        ·
          refine ⟨39034410568944828875480789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26022940379296552583653859 39034410568944828875480789)
          ·
            refine ⟨914868997709644426769081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 39034410568944828875480789 914868997709644426769081)
            ·
              refine ⟨686151748282233320076811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 914868997709644426769081 686151748282233320076811)
              ·
                refine ⟨1029227622423349980115217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686151748282233320076811 1029227622423349980115217)
                ·
                  refine ⟨771920716817512485086413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1029227622423349980115217 771920716817512485086413)
                  ·
                    refine ⟨289470268806567181907405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 771920716817512485086413 289470268806567181907405)
                    ·
                      rfl

theorem cell22_845612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 3].length) (baseStart_845612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845612 prefixEnd_845612 := by exact prefixLift 845612
  have htrace : WordTrace (prefixWord ++ tailWord_845612) baseStart_845612 baseEnd_845612 := by
    simpa [prefixWord, tailWord_845612, baseEnd_845612] using wordTrace_append hprefix tailTrace_845612
  have hstable : (prefixWord ++ tailWord_845612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845612).length < 2 ^ (prefixWord ++ tailWord_845612).sum := by decide
  have hdescent : baseEnd_845612 < baseStart_845612 := by decide
  rcases family_descends (prefixWord ++ tailWord_845612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845653 : List Nat := [1, 3, 2, 2, 2, 2, 1, 4, 5]
def baseStart_845653 : Nat := 118140960795 + 845653 * 2 ^ 59
def prefixEnd_845653 : Nat := 4983230072969 + 3 ^ 40 * 845653 * 2
def baseEnd_845653 : Nat := 96494767981485580544093

theorem tailTrace_845653 : CollatzResearch.WordTrace tailWord_845653 prefixEnd_845653 96494767981485580544093 := by
  unfold tailWord_845653
  simp only [CollatzResearch.WordTrace]
  refine ⟨30843498805351081879165613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20562332536900721252777075 30843498805351081879165613)
  ·
    refine ⟨11566312052006655704687105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30843498805351081879165613 11566312052006655704687105)
    ·
      refine ⟨8674734039004991778515329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11566312052006655704687105 8674734039004991778515329)
      ·
        refine ⟨6506050529253743833886497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8674734039004991778515329 6506050529253743833886497)
        ·
          refine ⟨4879537896940307875414873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6506050529253743833886497 4879537896940307875414873)
          ·
            refine ⟨3659653422705230906561155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4879537896940307875414873 3659653422705230906561155)
            ·
              refine ⟨5489480134057846359841733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3659653422705230906561155 5489480134057846359841733)
              ·
                refine ⟨1029277525135846192470325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5489480134057846359841733 1029277525135846192470325)
                ·
                  refine ⟨96494767981485580544093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1029277525135846192470325 96494767981485580544093)
                  ·
                    rfl

theorem cell22_845653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_845653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845653 prefixEnd_845653 := by exact prefixLift 845653
  have htrace : WordTrace (prefixWord ++ tailWord_845653) baseStart_845653 baseEnd_845653 := by
    simpa [prefixWord, tailWord_845653, baseEnd_845653] using wordTrace_append hprefix tailTrace_845653
  have hstable : (prefixWord ++ tailWord_845653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845653).length < 2 ^ (prefixWord ++ tailWord_845653).sum := by decide
  have hdescent : baseEnd_845653 < baseStart_845653 := by decide
  rcases family_descends (prefixWord ++ tailWord_845653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845683 : List Nat := [1, 1, 1, 2, 2, 1, 3, 6, 1, 4]
def baseStart_845683 : Nat := 118140960795 + 845683 * 2 ^ 59
def prefixEnd_845683 : Nat := 4983230072969 + 3 ^ 40 * 845683 * 2
def baseEnd_845683 : Nat := 289494573557546663382187

theorem tailTrace_845683 : CollatzResearch.WordTrace tailWord_845683 prefixEnd_845683 289494573557546663382187 := by
  unfold tailWord_845683
  simp only [CollatzResearch.WordTrace]
  refine ⟨30844592995242397002757703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20563061996828264668505135 30844592995242397002757703)
  ·
    refine ⟨46266889492863595504136555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30844592995242397002757703 46266889492863595504136555)
    ·
      refine ⟨69400334239295393256204833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46266889492863595504136555 69400334239295393256204833)
      ·
        refine ⟨52050250679471544942153625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69400334239295393256204833 52050250679471544942153625)
        ·
          refine ⟨39037688009603658706615219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52050250679471544942153625 39037688009603658706615219)
          ·
            refine ⟨58556532014405488059922829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39037688009603658706615219 58556532014405488059922829)
            ·
              refine ⟨21958699505402058022471061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58556532014405488059922829 21958699505402058022471061)
              ·
                refine ⟨1029314039315721469803331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21958699505402058022471061 1029314039315721469803331)
                ·
                  refine ⟨1543971058973582204704997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029314039315721469803331 1543971058973582204704997)
                  ·
                    refine ⟨289494573557546663382187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1543971058973582204704997 289494573557546663382187)
                    ·
                      rfl

theorem cell22_845683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 4].length) (baseStart_845683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845683 prefixEnd_845683 := by exact prefixLift 845683
  have htrace : WordTrace (prefixWord ++ tailWord_845683) baseStart_845683 baseEnd_845683 := by
    simpa [prefixWord, tailWord_845683, baseEnd_845683] using wordTrace_append hprefix tailTrace_845683
  have hstable : (prefixWord ++ tailWord_845683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845683).length < 2 ^ (prefixWord ++ tailWord_845683).sum := by decide
  have hdescent : baseEnd_845683 < baseStart_845683 := by decide
  rcases family_descends (prefixWord ++ tailWord_845683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845822 : List Nat := [4, 2, 2, 2, 1, 1, 1, 4, 5]
def baseStart_845822 : Nat := 118140960795 + 845822 * 2 ^ 59
def prefixEnd_845822 : Nat := 4983230072969 + 3 ^ 40 * 845822 * 2
def baseEnd_845822 : Nat := 96514052032732211385587

theorem tailTrace_845822 : CollatzResearch.WordTrace tailWord_845822 prefixEnd_845822 96514052032732211385587 := by
  unfold tailWord_845822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3856207842717352967758465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20566441827825882494711813 3856207842717352967758465)
  ·
    refine ⟨2892155882038014725818849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3856207842717352967758465 2892155882038014725818849)
    ·
      refine ⟨2169116911528511044364137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2892155882038014725818849 2169116911528511044364137)
      ·
        refine ⟨1626837683646383283273103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2169116911528511044364137 1626837683646383283273103)
        ·
          refine ⟨2440256525469574924909655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1626837683646383283273103 2440256525469574924909655)
          ·
            refine ⟨3660384788204362387364483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2440256525469574924909655 3660384788204362387364483)
            ·
              refine ⟨5490577182306543581046725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3660384788204362387364483 5490577182306543581046725)
              ·
                refine ⟨1029483221682476921446261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5490577182306543581046725 1029483221682476921446261)
                ·
                  refine ⟨96514052032732211385587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1029483221682476921446261 96514052032732211385587)
                  ·
                    rfl

theorem cell22_845822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_845822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845822 prefixEnd_845822 := by exact prefixLift 845822
  have htrace : WordTrace (prefixWord ++ tailWord_845822) baseStart_845822 baseEnd_845822 := by
    simpa [prefixWord, tailWord_845822, baseEnd_845822] using wordTrace_append hprefix tailTrace_845822
  have hstable : (prefixWord ++ tailWord_845822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845822).length < 2 ^ (prefixWord ++ tailWord_845822).sum := by decide
  have hdescent : baseEnd_845822 < baseStart_845822 := by decide
  rcases family_descends (prefixWord ++ tailWord_845822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845850 : List Nat := [3, 1, 1, 3, 1, 4, 1, 2, 6]
def baseStart_845850 : Nat := 118140960795 + 845850 * 2 ^ 59
def prefixEnd_845850 : Nat := 4983230072969 + 3 ^ 40 * 845850 * 2
def baseEnd_845850 : Nat := 96517247023471298152225

theorem tailTrace_845850 : CollatzResearch.WordTrace tailWord_845850 prefixEnd_845850 96517247023471298152225 := by
  unfold tailWord_845850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7712670996409346131021751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20567122657091589682724669 7712670996409346131021751)
  ·
    refine ⟨11569006494614019196532627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7712670996409346131021751 11569006494614019196532627)
    ·
      refine ⟨17353509741921028794798941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11569006494614019196532627 17353509741921028794798941)
      ·
        refine ⟨6507566153220385798049603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17353509741921028794798941 6507566153220385798049603)
        ·
          refine ⟨9761349229830578697074405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6507566153220385798049603 9761349229830578697074405)
          ·
            refine ⟨1830252980593233505701451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9761349229830578697074405 1830252980593233505701451)
            ·
              refine ⟨2745379470889850258552177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830252980593233505701451 2745379470889850258552177)
              ·
                refine ⟨2059034603167387693914133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2745379470889850258552177 2059034603167387693914133)
                ·
                  refine ⟨96517247023471298152225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2059034603167387693914133 96517247023471298152225)
                  ·
                    rfl

theorem cell22_845850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_845850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845850 prefixEnd_845850 := by exact prefixLift 845850
  have htrace : WordTrace (prefixWord ++ tailWord_845850) baseStart_845850 baseEnd_845850 := by
    simpa [prefixWord, tailWord_845850, baseEnd_845850] using wordTrace_append hprefix tailTrace_845850
  have hstable : (prefixWord ++ tailWord_845850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845850).length < 2 ^ (prefixWord ++ tailWord_845850).sum := by decide
  have hdescent : baseEnd_845850 < baseStart_845850 := by decide
  rcases family_descends (prefixWord ++ tailWord_845850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845912 : List Nat := [2, 1, 2, 2, 1, 6, 2, 6]
def baseStart_845912 : Nat := 118140960795 + 845912 * 2 ^ 59
def prefixEnd_845912 : Nat := 4983230072969 + 3 ^ 40 * 845912 * 2
def baseEnd_845912 : Nat := 32174773881940711045165

theorem tailTrace_845912 : CollatzResearch.WordTrace tailWord_845912 prefixEnd_845912 32174773881940711045165 := by
  unfold tailWord_845912
  simp only [CollatzResearch.WordTrace]
  refine ⟨15426472655706384556421995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20568630207608512741895993 15426472655706384556421995)
  ·
    refine ⟨23139708983559576834632993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15426472655706384556421995 23139708983559576834632993)
    ·
      refine ⟨17354781737669682625974745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23139708983559576834632993 17354781737669682625974745)
      ·
        refine ⟨13016086303252261969481059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17354781737669682625974745 13016086303252261969481059)
        ·
          refine ⟨19524129454878392954221589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13016086303252261969481059 19524129454878392954221589)
          ·
            refine ⟨915193568197424669729137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19524129454878392954221589 915193568197424669729137)
            ·
              refine ⟨686395176148068502296853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 915193568197424669729137 686395176148068502296853)
              ·
                refine ⟨32174773881940711045165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 686395176148068502296853 32174773881940711045165)
                ·
                  rfl

theorem cell22_845912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 6].length) (baseStart_845912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845912 prefixEnd_845912 := by exact prefixLift 845912
  have htrace : WordTrace (prefixWord ++ tailWord_845912) baseStart_845912 baseEnd_845912 := by
    simpa [prefixWord, tailWord_845912, baseEnd_845912] using wordTrace_append hprefix tailTrace_845912
  have hstable : (prefixWord ++ tailWord_845912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845912).length < 2 ^ (prefixWord ++ tailWord_845912).sum := by decide
  have hdescent : baseEnd_845912 < baseStart_845912 := by decide
  rcases family_descends (prefixWord ++ tailWord_845912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845957 : List Nat := [1, 3, 1, 1, 5, 2, 1, 3, 5]
def baseStart_845957 : Nat := 118140960795 + 845957 * 2 ^ 59
def prefixEnd_845957 : Nat := 4983230072969 + 3 ^ 40 * 845957 * 2
def baseEnd_845957 : Nat := 96529456452367094010449

theorem tailTrace_845957 : CollatzResearch.WordTrace tailWord_845957 prefixEnd_845957 96529456452367094010449 := by
  unfold tailWord_845957
  simp only [CollatzResearch.WordTrace]
  refine ⟨30854586596249741798232125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20569724397499827865488083 30854586596249741798232125)
  ·
    refine ⟨11570469973593653174337047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30854586596249741798232125 11570469973593653174337047)
    ·
      refine ⟨17355704960390479761505571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11570469973593653174337047 17355704960390479761505571)
      ·
        refine ⟨26033557440585719642258357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17355704960390479761505571 26033557440585719642258357)
        ·
          refine ⟨2440646010054911216461721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26033557440585719642258357 2440646010054911216461721)
          ·
            refine ⟨1830484507541183412346291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2440646010054911216461721 1830484507541183412346291)
            ·
              refine ⟨2745726761311775118519437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830484507541183412346291 2745726761311775118519437)
              ·
                refine ⟨1029647535491915669444789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2745726761311775118519437 1029647535491915669444789)
                ·
                  refine ⟨96529456452367094010449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1029647535491915669444789 96529456452367094010449)
                  ·
                    rfl

theorem cell22_845957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_845957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_845957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_845957 prefixEnd_845957 := by exact prefixLift 845957
  have htrace : WordTrace (prefixWord ++ tailWord_845957) baseStart_845957 baseEnd_845957 := by
    simpa [prefixWord, tailWord_845957, baseEnd_845957] using wordTrace_append hprefix tailTrace_845957
  have hstable : (prefixWord ++ tailWord_845957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845957).length < 2 ^ (prefixWord ++ tailWord_845957).sum := by decide
  have hdescent : baseEnd_845957 < baseStart_845957 := by decide
  rcases family_descends (prefixWord ++ tailWord_845957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846015 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 1, 6]
def baseStart_846015 : Nat := 118140960795 + 846015 * 2 ^ 59
def prefixEnd_846015 : Nat := 4983230072969 + 3 ^ 40 * 846015 * 2
def baseEnd_846015 : Nat := 289608223942408464081169

theorem tailTrace_846015 : CollatzResearch.WordTrace tailWord_846015 prefixEnd_846015 289608223942408464081169 := by
  unfold tailWord_846015
  simp only [CollatzResearch.WordTrace]
  refine ⟨30856702030039617703843499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20571134686693078469228999 30856702030039617703843499)
  ·
    refine ⟨46285053045059426555765249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30856702030039617703843499 46285053045059426555765249)
    ·
      refine ⟨34713789783794569916823937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46285053045059426555765249 34713789783794569916823937)
      ·
        refine ⟨26035342337845927437617953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34713789783794569916823937 26035342337845927437617953)
        ·
          refine ⟨19526506753384445578213465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26035342337845927437617953 19526506753384445578213465)
          ·
            refine ⟨14644880065038334183660099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19526506753384445578213465 14644880065038334183660099)
            ·
              refine ⟨21967320097557501275490149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14644880065038334183660099 21967320097557501275490149)
              ·
                refine ⟨4118872518292031489154403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21967320097557501275490149 4118872518292031489154403)
                ·
                  refine ⟨6178308777438047233731605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4118872518292031489154403 6178308777438047233731605)
                  ·
                    refine ⟨289608223942408464081169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6178308777438047233731605 289608223942408464081169)
                    ·
                      rfl

theorem cell22_846015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_846015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846015 prefixEnd_846015 := by exact prefixLift 846015
  have htrace : WordTrace (prefixWord ++ tailWord_846015) baseStart_846015 baseEnd_846015 := by
    simpa [prefixWord, tailWord_846015, baseEnd_846015] using wordTrace_append hprefix tailTrace_846015
  have hstable : (prefixWord ++ tailWord_846015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846015).length < 2 ^ (prefixWord ++ tailWord_846015).sum := by decide
  have hdescent : baseEnd_846015 < baseStart_846015 := by decide
  rcases family_descends (prefixWord ++ tailWord_846015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846038 : List Nat := [5, 2, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_846038 : Nat := 118140960795 + 846038 * 2 ^ 59
def prefixEnd_846038 : Nat := 4983230072969 + 3 ^ 40 * 846038 * 2
def baseEnd_846038 : Nat := 289616097312444070756099

theorem tailTrace_846038 : CollatzResearch.WordTrace tailWord_846038 prefixEnd_846038 289616097312444070756099 := by
  unfold tailWord_846038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1928596306809768289495673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20571693939304195087953845 1928596306809768289495673)
  ·
    refine ⟨1446447230107326217121755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1928596306809768289495673 1446447230107326217121755)
    ·
      refine ⟨2169670845160989325682633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1446447230107326217121755 2169670845160989325682633)
      ·
        refine ⟨1627253133870741994261975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2169670845160989325682633 1627253133870741994261975)
        ·
          refine ⟨2440879700806112991392963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1627253133870741994261975 2440879700806112991392963)
          ·
            refine ⟨3661319551209169487089445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2440879700806112991392963 3661319551209169487089445)
            ·
              refine ⟨686497415851719278829271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3661319551209169487089445 686497415851719278829271)
              ·
                refine ⟨1029746123777578918243907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686497415851719278829271 1029746123777578918243907)
                ·
                  refine ⟨1544619185666368377365861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029746123777578918243907 1544619185666368377365861)
                  ·
                    refine ⟨289616097312444070756099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1544619185666368377365861 289616097312444070756099)
                    ·
                      rfl

theorem cell22_846038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_846038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846038 prefixEnd_846038 := by exact prefixLift 846038
  have htrace : WordTrace (prefixWord ++ tailWord_846038) baseStart_846038 baseEnd_846038 := by
    simpa [prefixWord, tailWord_846038, baseEnd_846038] using wordTrace_append hprefix tailTrace_846038
  have hstable : (prefixWord ++ tailWord_846038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846038).length < 2 ^ (prefixWord ++ tailWord_846038).sum := by decide
  have hdescent : baseEnd_846038 < baseStart_846038 := by decide
  rcases family_descends (prefixWord ++ tailWord_846038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846051 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 4, 3]
def baseStart_846051 : Nat := 118140960795 + 846051 * 2 ^ 59
def prefixEnd_846051 : Nat := 4983230072969 + 3 ^ 40 * 846051 * 2
def baseEnd_846051 : Nat := 289620547478116370181059

theorem tailTrace_846051 : CollatzResearch.WordTrace tailWord_846051 prefixEnd_846051 289620547478116370181059 := by
  unfold tailWord_846051
  simp only [CollatzResearch.WordTrace]
  refine ⟨30858015057909195852154007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20572010038606130568102671 30858015057909195852154007)
  ·
    refine ⟨46287022586863793778231011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30858015057909195852154007 46287022586863793778231011)
    ·
      refine ⟨69430533880295690667346517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46287022586863793778231011 69430533880295690667346517)
      ·
        refine ⟨813639068909715125007967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 69430533880295690667346517 813639068909715125007967)
        ·
          refine ⟨1220458603364572687511951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813639068909715125007967 1220458603364572687511951)
          ·
            refine ⟨1830687905046859031267927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220458603364572687511951 1830687905046859031267927)
            ·
              refine ⟨2746031857570288546901891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830687905046859031267927 2746031857570288546901891)
              ·
                refine ⟨4119047786355432820352837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2746031857570288546901891 4119047786355432820352837)
                ·
                  refine ⟨772321459941643653816157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4119047786355432820352837 772321459941643653816157)
                  ·
                    refine ⟨289620547478116370181059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 772321459941643653816157 289620547478116370181059)
                    ·
                      rfl

theorem cell22_846051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 3].length) (baseStart_846051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846051 prefixEnd_846051 := by exact prefixLift 846051
  have htrace : WordTrace (prefixWord ++ tailWord_846051) baseStart_846051 baseEnd_846051 := by
    simpa [prefixWord, tailWord_846051, baseEnd_846051] using wordTrace_append hprefix tailTrace_846051
  have hstable : (prefixWord ++ tailWord_846051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846051).length < 2 ^ (prefixWord ++ tailWord_846051).sum := by decide
  have hdescent : baseEnd_846051 < baseStart_846051 := by decide
  rcases family_descends (prefixWord ++ tailWord_846051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846119 : List Nat := [1, 1, 8, 1, 2, 1, 2, 1, 2, 3]
def baseStart_846119 : Nat := 118140960795 + 846119 * 2 ^ 59
def prefixEnd_846119 : Nat := 4983230072969 + 3 ^ 40 * 846119 * 2
def baseEnd_846119 : Nat := 289643825267786859480851

theorem tailTrace_846119 : CollatzResearch.WordTrace tailWord_846119 prefixEnd_846119 289643825267786859480851 := by
  unfold tailWord_846119
  simp only [CollatzResearch.WordTrace]
  refine ⟨30860495221662843465629411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20573663481108562310419607 30860495221662843465629411)
  ·
    refine ⟨46290742832494265198444117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30860495221662843465629411 46290742832494265198444117)
    ·
      refine ⟨542469642568292170294267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 46290742832494265198444117 542469642568292170294267)
      ·
        refine ⟨813704463852438255441401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542469642568292170294267 813704463852438255441401)
        ·
          refine ⟨610278347889328691581051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 813704463852438255441401 610278347889328691581051)
          ·
            refine ⟨915417521833993037371577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610278347889328691581051 915417521833993037371577)
            ·
              refine ⟨686563141375494778028683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 915417521833993037371577 686563141375494778028683)
              ·
                refine ⟨1029844712063242167043025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686563141375494778028683 1029844712063242167043025)
                ·
                  refine ⟨772383534047431625282269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1029844712063242167043025 772383534047431625282269)
                  ·
                    refine ⟨289643825267786859480851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 772383534047431625282269 289643825267786859480851)
                    ·
                      rfl

theorem cell22_846119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_846119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846119 prefixEnd_846119 := by exact prefixLift 846119
  have htrace : WordTrace (prefixWord ++ tailWord_846119) baseStart_846119 baseEnd_846119 := by
    simpa [prefixWord, tailWord_846119, baseEnd_846119] using wordTrace_append hprefix tailTrace_846119
  have hstable : (prefixWord ++ tailWord_846119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846119).length < 2 ^ (prefixWord ++ tailWord_846119).sum := by decide
  have hdescent : baseEnd_846119 < baseStart_846119 := by decide
  rcases family_descends (prefixWord ++ tailWord_846119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846152 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 3, 5]
def baseStart_846152 : Nat := 118140960795 + 846152 * 2 ^ 59
def prefixEnd_846152 : Nat := 4983230072969 + 3 ^ 40 * 846152 * 2
def baseEnd_846152 : Nat := 289655121842185773405749

theorem tailTrace_846152 : CollatzResearch.WordTrace tailWord_846152 prefixEnd_846152 289655121842185773405749 := by
  unfold tailWord_846152
  simp only [CollatzResearch.WordTrace]
  refine ⟨15430849415271645050790355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20574465887028860067720473 15430849415271645050790355)
  ·
    refine ⟨23146274122907467576185533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15430849415271645050790355 23146274122907467576185533)
    ·
      refine ⟨8679852796090300341069575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23146274122907467576185533 8679852796090300341069575)
      ·
        refine ⟨13019779194135450511604363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8679852796090300341069575 13019779194135450511604363)
        ·
          refine ⟨19529668791203175767406545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13019779194135450511604363 19529668791203175767406545)
          ·
            refine ⟨14647251593402381825554909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19529668791203175767406545 14647251593402381825554909)
            ·
              refine ⟨5492719347525893184583091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14647251593402381825554909 5492719347525893184583091)
              ·
                refine ⟨8239079021288839776874637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5492719347525893184583091 8239079021288839776874637)
                ·
                  refine ⟨3089654632983314916327989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8239079021288839776874637 3089654632983314916327989)
                  ·
                    refine ⟨289655121842185773405749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3089654632983314916327989 289655121842185773405749)
                    ·
                      rfl

theorem cell22_846152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_846152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846152 prefixEnd_846152 := by exact prefixLift 846152
  have htrace : WordTrace (prefixWord ++ tailWord_846152) baseStart_846152 baseEnd_846152 := by
    simpa [prefixWord, tailWord_846152, baseEnd_846152] using wordTrace_append hprefix tailTrace_846152
  have hstable : (prefixWord ++ tailWord_846152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846152).length < 2 ^ (prefixWord ++ tailWord_846152).sum := by decide
  have hdescent : baseEnd_846152 < baseStart_846152 := by decide
  rcases family_descends (prefixWord ++ tailWord_846152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846156 : List Nat := [2, 2, 1, 3, 2, 1, 5, 1, 1, 4]
def baseStart_846156 : Nat := 118140960795 + 846156 * 2 ^ 59
def prefixEnd_846156 : Nat := 4983230072969 + 3 ^ 40 * 846156 * 2
def baseEnd_846156 : Nat := 289656491123931096305737

theorem tailTrace_846156 : CollatzResearch.WordTrace tailWord_846156 prefixEnd_846156 289656491123931096305737 := by
  unfold tailWord_846156
  simp only [CollatzResearch.WordTrace]
  refine ⟨15430922361264399392363161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20574563148352532523150881 15430922361264399392363161)
  ·
    refine ⟨11573191770948299544272371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15430922361264399392363161 11573191770948299544272371)
    ·
      refine ⟨17359787656422449316408557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11573191770948299544272371 17359787656422449316408557)
      ·
        refine ⟨6509920371158418493653209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17359787656422449316408557 6509920371158418493653209)
        ·
          refine ⟨4882440278368813870239907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6509920371158418493653209 4882440278368813870239907)
          ·
            refine ⟨7323660417553220805359861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4882440278368813870239907 7323660417553220805359861)
            ·
              refine ⟨686593164145614450502487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7323660417553220805359861 686593164145614450502487)
              ·
                refine ⟨1029889746218421675753731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686593164145614450502487 1029889746218421675753731)
                ·
                  refine ⟨1544834619327632513630597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029889746218421675753731 1544834619327632513630597)
                  ·
                    refine ⟨289656491123931096305737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1544834619327632513630597 289656491123931096305737)
                    ·
                      rfl

theorem cell22_846156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 1, 4].length) (baseStart_846156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846156 prefixEnd_846156 := by exact prefixLift 846156
  have htrace : WordTrace (prefixWord ++ tailWord_846156) baseStart_846156 baseEnd_846156 := by
    simpa [prefixWord, tailWord_846156, baseEnd_846156] using wordTrace_append hprefix tailTrace_846156
  have hstable : (prefixWord ++ tailWord_846156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846156).length < 2 ^ (prefixWord ++ tailWord_846156).sum := by decide
  have hdescent : baseEnd_846156 < baseStart_846156 := by decide
  rcases family_descends (prefixWord ++ tailWord_846156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846186 : List Nat := [3, 1, 3, 3, 1, 2, 2, 1, 1, 5]
def baseStart_846186 : Nat := 118140960795 + 846186 * 2 ^ 59
def prefixEnd_846186 : Nat := 4983230072969 + 3 ^ 40 * 846186 * 2
def baseEnd_846186 : Nat := 289666760737021018055645

theorem tailTrace_846186 : CollatzResearch.WordTrace tailWord_846186 prefixEnd_846186 289666760737021018055645 := by
  unfold tailWord_846186
  simp only [CollatzResearch.WordTrace]
  refine ⟨7715734728105028477079603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20575292608280075938878941 7715734728105028477079603)
  ·
    refine ⟨11573602092157542715619405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7715734728105028477079603 11573602092157542715619405)
    ·
      refine ⟨4340100784559078518357277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11573602092157542715619405 4340100784559078518357277)
      ·
        refine ⟨1627537794209654444383979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4340100784559078518357277 1627537794209654444383979)
        ·
          refine ⟨2441306691314481666575969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1627537794209654444383979 2441306691314481666575969)
          ·
            refine ⟨1830980018485861249931977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2441306691314481666575969 1830980018485861249931977)
            ·
              refine ⟨1373235013864395937448983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1830980018485861249931977 1373235013864395937448983)
              ·
                refine ⟨2059852520796593906173475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373235013864395937448983 2059852520796593906173475)
                ·
                  refine ⟨3089778781194890859260213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059852520796593906173475 3089778781194890859260213)
                  ·
                    refine ⟨289666760737021018055645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3089778781194890859260213 289666760737021018055645)
                    ·
                      rfl

theorem cell22_846186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_846186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846186 prefixEnd_846186 := by exact prefixLift 846186
  have htrace : WordTrace (prefixWord ++ tailWord_846186) baseStart_846186 baseEnd_846186 := by
    simpa [prefixWord, tailWord_846186, baseEnd_846186] using wordTrace_append hprefix tailTrace_846186
  have hstable : (prefixWord ++ tailWord_846186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846186).length < 2 ^ (prefixWord ++ tailWord_846186).sum := by decide
  have hdescent : baseEnd_846186 < baseStart_846186 := by decide
  rcases family_descends (prefixWord ++ tailWord_846186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846244 : List Nat := [2, 3, 1, 2, 1, 1, 2, 5, 5]
def baseStart_846244 : Nat := 118140960795 + 846244 * 2 ^ 59
def prefixEnd_846244 : Nat := 4983230072969 + 3 ^ 40 * 846244 * 2
def baseEnd_846244 : Nat := 96562205107442733368489

theorem tailTrace_846244 : CollatzResearch.WordTrace tailWord_846244 prefixEnd_846244 96562205107442733368489 := by
  unfold tailWord_846244
  simp only [CollatzResearch.WordTrace]
  refine ⟨15432527173104994906964893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20576702897473326542619857 15432527173104994906964893)
  ·
    refine ⟨5787197689914373090111835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15432527173104994906964893 5787197689914373090111835)
    ·
      refine ⟨8680796534871559635167753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5787197689914373090111835 8680796534871559635167753)
      ·
        refine ⟨6510597401153669726375815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8680796534871559635167753 6510597401153669726375815)
        ·
          refine ⟨9765896101730504589563723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6510597401153669726375815 9765896101730504589563723)
          ·
            refine ⟨14648844152595756884345585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9765896101730504589563723 14648844152595756884345585)
            ·
              refine ⟨10986633114446817663259189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14648844152595756884345585 10986633114446817663259189)
              ·
                refine ⟨1029996854479389155930549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10986633114446817663259189 1029996854479389155930549)
                ·
                  refine ⟨96562205107442733368489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1029996854479389155930549 96562205107442733368489)
                  ·
                    rfl

theorem cell22_846244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_846244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846244 prefixEnd_846244 := by exact prefixLift 846244
  have htrace : WordTrace (prefixWord ++ tailWord_846244) baseStart_846244 baseEnd_846244 := by
    simpa [prefixWord, tailWord_846244, baseEnd_846244] using wordTrace_append hprefix tailTrace_846244
  have hstable : (prefixWord ++ tailWord_846244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846244).length < 2 ^ (prefixWord ++ tailWord_846244).sum := by decide
  have hdescent : baseEnd_846244 < baseStart_846244 := by decide
  rcases family_descends (prefixWord ++ tailWord_846244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846248 : List Nat := [2, 1, 6, 1, 1, 1, 2, 2, 3, 3]
def baseStart_846248 : Nat := 118140960795 + 846248 * 2 ^ 59
def prefixEnd_846248 : Nat := 4983230072969 + 3 ^ 40 * 846248 * 2
def baseEnd_846248 : Nat := 289687984604073523005455

theorem tailTrace_846248 : CollatzResearch.WordTrace tailWord_846248 prefixEnd_846248 289687984604073523005455 := by
  unfold tailWord_846248
  simp only [CollatzResearch.WordTrace]
  refine ⟨15432600119097749248537699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20576800158796998998050265 15432600119097749248537699)
  ·
    refine ⟨23148900178646623872806549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15432600119097749248537699 23148900178646623872806549)
    ·
      refine ⟨1085104695874060494037807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23148900178646623872806549 1085104695874060494037807)
      ·
        refine ⟨1627657043811090741056711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1085104695874060494037807 1627657043811090741056711)
        ·
          refine ⟨2441485565716636111585067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1627657043811090741056711 2441485565716636111585067)
          ·
            refine ⟨3662228348574954167377601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2441485565716636111585067 3662228348574954167377601)
            ·
              refine ⟨2746671261431215625533201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3662228348574954167377601 2746671261431215625533201)
              ·
                refine ⟨2060003446073411719149901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2746671261431215625533201 2060003446073411719149901)
                ·
                  refine ⟨772501292277529394681213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2060003446073411719149901 772501292277529394681213)
                  ·
                    refine ⟨289687984604073523005455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 772501292277529394681213 289687984604073523005455)
                    ·
                      rfl

theorem cell22_846248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_846248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846248 prefixEnd_846248 := by exact prefixLift 846248
  have htrace : WordTrace (prefixWord ++ tailWord_846248) baseStart_846248 baseEnd_846248 := by
    simpa [prefixWord, tailWord_846248, baseEnd_846248] using wordTrace_append hprefix tailTrace_846248
  have hstable : (prefixWord ++ tailWord_846248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846248).length < 2 ^ (prefixWord ++ tailWord_846248).sum := by decide
  have hdescent : baseEnd_846248 < baseStart_846248 := by decide
  rcases family_descends (prefixWord ++ tailWord_846248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846265 : List Nat := [1, 2, 1, 4, 3, 3, 1, 3, 1, 3]
def baseStart_846265 : Nat := 118140960795 + 846265 * 2 ^ 59
def prefixEnd_846265 : Nat := 4983230072969 + 3 ^ 40 * 846265 * 2
def baseEnd_846265 : Nat := 289693804051491145330403

theorem tailTrace_846265 : CollatzResearch.WordTrace tailWord_846265 prefixEnd_846265 289693804051491145330403 := by
  unfold tailWord_846265
  simp only [CollatzResearch.WordTrace]
  refine ⟨30865820279133910400444249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20577213519422606933629499 30865820279133910400444249)
  ·
    refine ⟨23149365209350432800333187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30865820279133910400444249 23149365209350432800333187)
    ·
      refine ⟨34724047814025649200499781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23149365209350432800333187 34724047814025649200499781)
      ·
        refine ⟨6510758965129809225093709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34724047814025649200499781 6510758965129809225093709)
        ·
          refine ⟨2441534611923678459410141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6510758965129809225093709 2441534611923678459410141)
          ·
            refine ⟨915575479471379422278803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2441534611923678459410141 915575479471379422278803)
            ·
              refine ⟨1373363219207069133418205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915575479471379422278803 1373363219207069133418205)
              ·
                refine ⟨515011207202650925031827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1373363219207069133418205 515011207202650925031827)
                ·
                  refine ⟨772516810803976387547741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515011207202650925031827 772516810803976387547741)
                  ·
                    refine ⟨289693804051491145330403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 772516810803976387547741 289693804051491145330403)
                    ·
                      rfl

theorem cell22_846265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 1, 3].length) (baseStart_846265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846265 prefixEnd_846265 := by exact prefixLift 846265
  have htrace : WordTrace (prefixWord ++ tailWord_846265) baseStart_846265 baseEnd_846265 := by
    simpa [prefixWord, tailWord_846265, baseEnd_846265] using wordTrace_append hprefix tailTrace_846265
  have hstable : (prefixWord ++ tailWord_846265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846265).length < 2 ^ (prefixWord ++ tailWord_846265).sum := by decide
  have hdescent : baseEnd_846265 < baseStart_846265 := by decide
  rcases family_descends (prefixWord ++ tailWord_846265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846304 : List Nat := [2, 1, 1, 3, 1, 1, 4, 3, 1, 5]
def baseStart_846304 : Nat := 118140960795 + 846304 * 2 ^ 59
def prefixEnd_846304 : Nat := 4983230072969 + 3 ^ 40 * 846304 * 2
def baseEnd_846304 : Nat := 289707154548508043605283

theorem tailTrace_846304 : CollatzResearch.WordTrace tailWord_846304 prefixEnd_846304 289707154548508043605283 := by
  unfold tailWord_846304
  simp only [CollatzResearch.WordTrace]
  refine ⟨15433621362996310030556983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20578161817328413374075977 15433621362996310030556983)
  ·
    refine ⟨23150432044494465045835475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15433621362996310030556983 23150432044494465045835475)
    ·
      refine ⟨34725648066741697568753213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23150432044494465045835475 34725648066741697568753213)
      ·
        refine ⟨13022118025028136588282455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34725648066741697568753213 13022118025028136588282455)
        ·
          refine ⟨19533177037542204882423683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13022118025028136588282455 19533177037542204882423683)
          ·
            refine ⟨29299765556313307323635525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19533177037542204882423683 29299765556313307323635525)
            ·
              refine ⟨5493706041808745123181661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29299765556313307323635525 5493706041808745123181661)
              ·
                refine ⟨2060139765678279421193123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5493706041808745123181661 2060139765678279421193123)
                ·
                  refine ⟨3090209648517419131789685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060139765678279421193123 3090209648517419131789685)
                  ·
                    refine ⟨289707154548508043605283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3090209648517419131789685 289707154548508043605283)
                    ·
                      rfl

theorem cell22_846304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_846304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846304 prefixEnd_846304 := by exact prefixLift 846304
  have htrace : WordTrace (prefixWord ++ tailWord_846304) baseStart_846304 baseEnd_846304 := by
    simpa [prefixWord, tailWord_846304, baseEnd_846304] using wordTrace_append hprefix tailTrace_846304
  have hstable : (prefixWord ++ tailWord_846304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846304).length < 2 ^ (prefixWord ++ tailWord_846304).sum := by decide
  have hdescent : baseEnd_846304 < baseStart_846304 := by decide
  rcases family_descends (prefixWord ++ tailWord_846304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846334 : List Nat := [4, 2, 2, 14]
def baseStart_846334 : Nat := 118140960795 + 846334 * 2 ^ 59
def prefixEnd_846334 : Nat := 4983230072969 + 3 ^ 40 * 846334 * 2
def baseEnd_846334 : Nat := 397417591442521214479

theorem tailTrace_846334 : CollatzResearch.WordTrace tailWord_846334 prefixEnd_846334 397417591442521214479 := by
  unfold tailWord_846334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3858542114485491898088257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20578891277255956789804037 3858542114485491898088257)
  ·
    refine ⟨2893906585864118923566193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3858542114485491898088257 2893906585864118923566193)
    ·
      refine ⟨2170429939398089192674645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2893906585864118923566193 2170429939398089192674645)
      ·
        refine ⟨397417591442521214479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 2170429939398089192674645 397417591442521214479)
        ·
          rfl

theorem cell22_846334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 14].length) (baseStart_846334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846334 prefixEnd_846334 := by exact prefixLift 846334
  have htrace : WordTrace (prefixWord ++ tailWord_846334) baseStart_846334 baseEnd_846334 := by
    simpa [prefixWord, tailWord_846334, baseEnd_846334] using wordTrace_append hprefix tailTrace_846334
  have hstable : (prefixWord ++ tailWord_846334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846334).length < 2 ^ (prefixWord ++ tailWord_846334).sum := by decide
  have hdescent : baseEnd_846334 < baseStart_846334 := by decide
  rcases family_descends (prefixWord ++ tailWord_846334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846340 : List Nat := [2, 3, 2, 3, 1, 1, 4, 2, 4]
def baseStart_846340 : Nat := 118140960795 + 846340 * 2 ^ 59
def prefixEnd_846340 : Nat := 4983230072969 + 3 ^ 40 * 846340 * 2
def baseEnd_846340 : Nat := 96573159361405316568391

theorem tailTrace_846340 : CollatzResearch.WordTrace tailWord_846340 prefixEnd_846340 96573159361405316568391 := by
  unfold tailWord_846340
  simp only [CollatzResearch.WordTrace]
  refine ⟨15434277876931099104712237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20579037169241465472949649 15434277876931099104712237)
  ·
    refine ⟨5787854203849162164267089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15434277876931099104712237 5787854203849162164267089)
    ·
      refine ⟨4340890652886871623200317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5787854203849162164267089 4340890652886871623200317)
      ·
        refine ⟨1627833994832576858700119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4340890652886871623200317 1627833994832576858700119)
        ·
          refine ⟨2441750992248865288050179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1627833994832576858700119 2441750992248865288050179)
          ·
            refine ⟨3662626488373297932075269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2441750992248865288050179 3662626488373297932075269)
            ·
              refine ⟨686742466569993362264113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3662626488373297932075269 686742466569993362264113)
              ·
                refine ⟨515056849927495021698085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 686742466569993362264113 515056849927495021698085)
                ·
                  refine ⟨96573159361405316568391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 515056849927495021698085 96573159361405316568391)
                  ·
                    rfl

theorem cell22_846340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_846340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846340 prefixEnd_846340 := by exact prefixLift 846340
  have htrace : WordTrace (prefixWord ++ tailWord_846340) baseStart_846340 baseEnd_846340 := by
    simpa [prefixWord, tailWord_846340, baseEnd_846340] using wordTrace_append hprefix tailTrace_846340
  have hstable : (prefixWord ++ tailWord_846340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846340).length < 2 ^ (prefixWord ++ tailWord_846340).sum := by decide
  have hdescent : baseEnd_846340 < baseStart_846340 := by decide
  rcases family_descends (prefixWord ++ tailWord_846340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846368 : List Nat := [2, 1, 1, 6, 2, 1, 3, 6]
def baseStart_846368 : Nat := 118140960795 + 846368 * 2 ^ 59
def prefixEnd_846368 : Nat := 4983230072969 + 3 ^ 40 * 846368 * 2
def baseEnd_846368 : Nat := 32192118117381467778343

theorem tailTrace_846368 : CollatzResearch.WordTrace tailWord_846368 prefixEnd_846368 32192118117381467778343 := by
  unfold tailWord_846368
  simp only [CollatzResearch.WordTrace]
  refine ⟨15434788498880379495721879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20579717998507172660962505 15434788498880379495721879)
  ·
    refine ⟨23152182748320569243582819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15434788498880379495721879 23152182748320569243582819)
    ·
      refine ⟨34728274122480853865374229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23152182748320569243582819 34728274122480853865374229)
      ·
        refine ⟨1627887849491290024939417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34728274122480853865374229 1627887849491290024939417)
        ·
          refine ⟨1220915887118467518704563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1627887849491290024939417 1220915887118467518704563)
          ·
            refine ⟨1831373830677701278056845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220915887118467518704563 1831373830677701278056845)
            ·
              refine ⟨686765186504137979271317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1831373830677701278056845 686765186504137979271317)
              ·
                refine ⟨32192118117381467778343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 686765186504137979271317 32192118117381467778343)
                ·
                  rfl

theorem cell22_846368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 6].length) (baseStart_846368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846368 prefixEnd_846368 := by exact prefixLift 846368
  have htrace : WordTrace (prefixWord ++ tailWord_846368) baseStart_846368 baseEnd_846368 := by
    simpa [prefixWord, tailWord_846368, baseEnd_846368] using wordTrace_append hprefix tailTrace_846368
  have hstable : (prefixWord ++ tailWord_846368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846368).length < 2 ^ (prefixWord ++ tailWord_846368).sum := by decide
  have hdescent : baseEnd_846368 < baseStart_846368 := by decide
  rcases family_descends (prefixWord ++ tailWord_846368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846396 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 7]
def baseStart_846396 : Nat := 118140960795 + 846396 * 2 ^ 59
def prefixEnd_846396 : Nat := 4983230072969 + 3 ^ 40 * 846396 * 2
def baseEnd_846396 : Nat := 96579549342883490101667

theorem tailTrace_846396 : CollatzResearch.WordTrace tailWord_846396 prefixEnd_846396 96579549342883490101667 := by
  unfold tailWord_846396
  simp only [CollatzResearch.WordTrace]
  refine ⟨15435299120829659886731521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20580398827772879848975361 15435299120829659886731521)
  ·
    refine ⟨11576474340622244915048641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15435299120829659886731521 11576474340622244915048641)
    ·
      refine ⟨8682355755466683686286481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11576474340622244915048641 8682355755466683686286481)
      ·
        refine ⟨6511766816600012764714861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8682355755466683686286481 6511766816600012764714861)
        ·
          refine ⟨2441912556225004786768073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6511766816600012764714861 2441912556225004786768073)
          ·
            refine ⟨1831434417168753590076055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2441912556225004786768073 1831434417168753590076055)
            ·
              refine ⟨2747151625753130385114083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1831434417168753590076055 2747151625753130385114083)
              ·
                refine ⟨4120727438629695577671125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2747151625753130385114083 4120727438629695577671125)
                ·
                  refine ⟨96579549342883490101667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4120727438629695577671125 96579549342883490101667)
                  ·
                    rfl

theorem cell22_846396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_846396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846396 prefixEnd_846396 := by exact prefixLift 846396
  have htrace : WordTrace (prefixWord ++ tailWord_846396) baseStart_846396 baseEnd_846396 := by
    simpa [prefixWord, tailWord_846396, baseEnd_846396] using wordTrace_append hprefix tailTrace_846396
  have hstable : (prefixWord ++ tailWord_846396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846396).length < 2 ^ (prefixWord ++ tailWord_846396).sum := by decide
  have hdescent : baseEnd_846396 < baseStart_846396 := by decide
  rcases family_descends (prefixWord ++ tailWord_846396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846471 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 4, 4]
def baseStart_846471 : Nat := 118140960795 + 846471 * 2 ^ 59
def prefixEnd_846471 : Nat := 4983230072969 + 3 ^ 40 * 846471 * 2
def baseEnd_846471 : Nat := 289764322061375274679771

theorem tailTrace_846471 : CollatzResearch.WordTrace tailWord_846471 prefixEnd_846471 289764322061375274679771 := by
  unfold tailWord_846471
  simp only [CollatzResearch.WordTrace]
  refine ⟨30873333716387607582443267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20582222477591738388295511 30873333716387607582443267)
  ·
    refine ⟨46310000574581411373664901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30873333716387607582443267 46310000574581411373664901)
    ·
      refine ⟨8683125107734014632562169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46310000574581411373664901 8683125107734014632562169)
      ·
        refine ⟨6512343830800510974421627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8683125107734014632562169 6512343830800510974421627)
        ·
          refine ⟨9768515746200766461632441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6512343830800510974421627 9768515746200766461632441)
          ·
            refine ⟨7326386809650574846224331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9768515746200766461632441 7326386809650574846224331)
            ·
              refine ⟨10989580214475862269336497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7326386809650574846224331 10989580214475862269336497)
              ·
                refine ⟨8242185160856896702002373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10989580214475862269336497 8242185160856896702002373)
                ·
                  refine ⟨1545409717660668131625445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8242185160856896702002373 1545409717660668131625445)
                  ·
                    refine ⟨289764322061375274679771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1545409717660668131625445 289764322061375274679771)
                    ·
                      rfl

theorem cell22_846471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_846471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846471 prefixEnd_846471 := by exact prefixLift 846471
  have htrace : WordTrace (prefixWord ++ tailWord_846471) baseStart_846471 baseEnd_846471 := by
    simpa [prefixWord, tailWord_846471, baseEnd_846471] using wordTrace_append hprefix tailTrace_846471
  have hstable : (prefixWord ++ tailWord_846471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846471).length < 2 ^ (prefixWord ++ tailWord_846471).sum := by decide
  have hdescent : baseEnd_846471 < baseStart_846471 := by decide
  rcases family_descends (prefixWord ++ tailWord_846471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846488 : List Nat := [2, 1, 2, 4, 1, 1, 4, 1, 2, 4]
def baseStart_846488 : Nat := 118140960795 + 846488 * 2 ^ 59
def prefixEnd_846488 : Nat := 4983230072969 + 3 ^ 40 * 846488 * 2
def baseEnd_846488 : Nat := 289770141508792897004719

theorem tailTrace_846488 : CollatzResearch.WordTrace tailWord_846488 prefixEnd_846488 289770141508792897004719 := by
  unfold tailWord_846488
  simp only [CollatzResearch.WordTrace]
  refine ⟨15436976878663009742906059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20582635838217346323874745 15436976878663009742906059)
  ·
    refine ⟨23155465317994514614359089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15436976878663009742906059 23155465317994514614359089)
    ·
      refine ⟨17366598988495885960769317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23155465317994514614359089 17366598988495885960769317)
      ·
        refine ⟨3256237310342978617644247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17366598988495885960769317 3256237310342978617644247)
        ·
          refine ⟨4884355965514467926466371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3256237310342978617644247 4884355965514467926466371)
          ·
            refine ⟨7326533948271701889699557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4884355965514467926466371 7326533948271701889699557)
            ·
              refine ⟨1373725115300944104318667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7326533948271701889699557 1373725115300944104318667)
              ·
                refine ⟨2060587672951416156478001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373725115300944104318667 2060587672951416156478001)
                ·
                  refine ⟨1545440754713562117358501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2060587672951416156478001 1545440754713562117358501)
                  ·
                    refine ⟨289770141508792897004719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1545440754713562117358501 289770141508792897004719)
                    ·
                      rfl

theorem cell22_846488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_846488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846488 prefixEnd_846488 := by exact prefixLift 846488
  have htrace : WordTrace (prefixWord ++ tailWord_846488) baseStart_846488 baseEnd_846488 := by
    simpa [prefixWord, tailWord_846488, baseEnd_846488] using wordTrace_append hprefix tailTrace_846488
  have hstable : (prefixWord ++ tailWord_846488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846488).length < 2 ^ (prefixWord ++ tailWord_846488).sum := by decide
  have hdescent : baseEnd_846488 < baseStart_846488 := by decide
  rcases family_descends (prefixWord ++ tailWord_846488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846490 : List Nat := [3, 1, 1, 6, 1, 1, 1, 2, 1, 5]
def baseStart_846490 : Nat := 118140960795 + 846490 * 2 ^ 59
def prefixEnd_846490 : Nat := 4983230072969 + 3 ^ 40 * 846490 * 2
def baseEnd_846490 : Nat := 289770826149665558454713

theorem tailTrace_846490 : CollatzResearch.WordTrace tailWord_846490 prefixEnd_846490 289770826149665558454713 := by
  unfold tailWord_846490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7718506675829693456846231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20582684468879182551589949 7718506675829693456846231)
  ·
    refine ⟨11577760013744540185269347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7718506675829693456846231 11577760013744540185269347)
    ·
      refine ⟨17366640020616810277904021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11577760013744540185269347 17366640020616810277904021)
      ·
        refine ⟨814061250966412981776751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17366640020616810277904021 814061250966412981776751)
        ·
          refine ⟨1221091876449619472665127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814061250966412981776751 1221091876449619472665127)
          ·
            refine ⟨1831637814674429208997691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221091876449619472665127 1831637814674429208997691)
            ·
              refine ⟨2747456722011643813496537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1831637814674429208997691 2747456722011643813496537)
              ·
                refine ⟨2060592541508732860122403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2747456722011643813496537 2060592541508732860122403)
                ·
                  refine ⟨3090888812263099290183605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060592541508732860122403 3090888812263099290183605)
                  ·
                    refine ⟨289770826149665558454713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3090888812263099290183605 289770826149665558454713)
                    ·
                      rfl

theorem cell22_846490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_846490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846490 prefixEnd_846490 := by exact prefixLift 846490
  have htrace : WordTrace (prefixWord ++ tailWord_846490) baseStart_846490 baseEnd_846490 := by
    simpa [prefixWord, tailWord_846490, baseEnd_846490] using wordTrace_append hprefix tailTrace_846490
  have hstable : (prefixWord ++ tailWord_846490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846490).length < 2 ^ (prefixWord ++ tailWord_846490).sum := by decide
  have hdescent : baseEnd_846490 < baseStart_846490 := by decide
  rcases family_descends (prefixWord ++ tailWord_846490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846503 : List Nat := [1, 1, 6, 3, 1, 10]
def baseStart_846503 : Nat := 118140960795 + 846503 * 2 ^ 59
def prefixEnd_846503 : Nat := 4983230072969 + 3 ^ 40 * 846503 * 2
def baseEnd_846503 : Nat := 3577472547102936517033

theorem tailTrace_846503 : CollatzResearch.WordTrace tailWord_846503 prefixEnd_846503 3577472547102936517033 := by
  unfold tailWord_846503
  simp only [CollatzResearch.WordTrace]
  refine ⟨30874500852271677047608163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20583000568181118031738775 30874500852271677047608163)
  ·
    refine ⟨46311751278407515571412245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30874500852271677047608163 46311751278407515571412245)
    ·
      refine ⟨2170863341175352292409949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46311751278407515571412245 2170863341175352292409949)
      ·
        refine ⟨814073752940757109653731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2170863341175352292409949 814073752940757109653731)
        ·
          refine ⟨1221110629411135664480597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814073752940757109653731 1221110629411135664480597)
          ·
            refine ⟨3577472547102936517033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1221110629411135664480597 3577472547102936517033)
            ·
              rfl

theorem cell22_846503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 10].length) (baseStart_846503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846503 prefixEnd_846503 := by exact prefixLift 846503
  have htrace : WordTrace (prefixWord ++ tailWord_846503) baseStart_846503 baseEnd_846503 := by
    simpa [prefixWord, tailWord_846503, baseEnd_846503] using wordTrace_append hprefix tailTrace_846503
  have hstable : (prefixWord ++ tailWord_846503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846503).length < 2 ^ (prefixWord ++ tailWord_846503).sum := by decide
  have hdescent : baseEnd_846503 < baseStart_846503 := by decide
  rcases family_descends (prefixWord ++ tailWord_846503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846552 : List Nat := [2, 1, 2, 2, 3, 3, 2, 3, 1, 3]
def baseStart_846552 : Nat := 118140960795 + 846552 * 2 ^ 59
def prefixEnd_846552 : Nat := 4983230072969 + 3 ^ 40 * 846552 * 2
def baseEnd_846552 : Nat := 289792050016718063404523

theorem tailTrace_846552 : CollatzResearch.WordTrace tailWord_846552 prefixEnd_846552 289792050016718063404523 := by
  unfold tailWord_846552
  simp only [CollatzResearch.WordTrace]
  refine ⟨15438144014547079208070955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20584192019396105610761273 15438144014547079208070955)
  ·
    refine ⟨23157216021820618812106433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15438144014547079208070955 23157216021820618812106433)
    ·
      refine ⟨17367912016365464109079825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23157216021820618812106433 17367912016365464109079825)
      ·
        refine ⟨13025934012274098081809869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17367912016365464109079825 13025934012274098081809869)
        ·
          refine ⟨4884725254602786780678701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13025934012274098081809869 4884725254602786780678701)
          ·
            refine ⟨1831771970476045042754513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4884725254602786780678701 1831771970476045042754513)
            ·
              refine ⟨1373828977857033782065885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1831771970476045042754513 1373828977857033782065885)
              ·
                refine ⟨515185866696387668274707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1373828977857033782065885 515185866696387668274707)
                ·
                  refine ⟨772778800044581502412061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515185866696387668274707 772778800044581502412061)
                  ·
                    refine ⟨289792050016718063404523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 772778800044581502412061 289792050016718063404523)
                    ·
                      rfl

theorem cell22_846552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 1, 3].length) (baseStart_846552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846552 prefixEnd_846552 := by exact prefixLift 846552
  have htrace : WordTrace (prefixWord ++ tailWord_846552) baseStart_846552 baseEnd_846552 := by
    simpa [prefixWord, tailWord_846552, baseEnd_846552] using wordTrace_append hprefix tailTrace_846552
  have hstable : (prefixWord ++ tailWord_846552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846552).length < 2 ^ (prefixWord ++ tailWord_846552).sum := by decide
  have hdescent : baseEnd_846552 < baseStart_846552 := by decide
  rcases family_descends (prefixWord ++ tailWord_846552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846563 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 2, 5]
def baseStart_846563 : Nat := 118140960795 + 846563 * 2 ^ 59
def prefixEnd_846563 : Nat := 4983230072969 + 3 ^ 40 * 846563 * 2
def baseEnd_846563 : Nat := 289795815541517701379489

theorem tailTrace_846563 : CollatzResearch.WordTrace tailWord_846563 prefixEnd_846563 289795815541517701379489 := by
  unfold tailWord_846563
  simp only [CollatzResearch.WordTrace]
  refine ⟨30876689232054307294792343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20584459488036204863194895 30876689232054307294792343)
  ·
    refine ⟨46315033848081460942188515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30876689232054307294792343 46315033848081460942188515)
    ·
      refine ⟨69472550772122191413282773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46315033848081460942188515 69472550772122191413282773)
      ·
        refine ⟨1628262908721613861248815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 69472550772122191413282773 1628262908721613861248815)
        ·
          refine ⟨2442394363082420791873223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628262908721613861248815 2442394363082420791873223)
          ·
            refine ⟨3663591544623631187809835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2442394363082420791873223 3663591544623631187809835)
            ·
              refine ⟨5495387316935446781714753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3663591544623631187809835 5495387316935446781714753)
              ·
                refine ⟨4121540487701585086286065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5495387316935446781714753 4121540487701585086286065)
                ·
                  refine ⟨3091155365776188814714549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4121540487701585086286065 3091155365776188814714549)
                  ·
                    refine ⟨289795815541517701379489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3091155365776188814714549 289795815541517701379489)
                    ·
                      rfl

theorem cell22_846563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 5].length) (baseStart_846563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846563 prefixEnd_846563 := by exact prefixLift 846563
  have htrace : WordTrace (prefixWord ++ tailWord_846563) baseStart_846563 baseEnd_846563 := by
    simpa [prefixWord, tailWord_846563, baseEnd_846563] using wordTrace_append hprefix tailTrace_846563
  have hstable : (prefixWord ++ tailWord_846563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846563).length < 2 ^ (prefixWord ++ tailWord_846563).sum := by decide
  have hdescent : baseEnd_846563 < baseStart_846563 := by decide
  rcases family_descends (prefixWord ++ tailWord_846563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846565 : List Nat := [1, 3, 1, 4, 1, 4, 1, 2, 5]
def baseStart_846565 : Nat := 118140960795 + 846565 * 2 ^ 59
def prefixEnd_846565 : Nat := 4983230072969 + 3 ^ 40 * 846565 * 2
def baseEnd_846565 : Nat := 96598833394130120943161

theorem tailTrace_846565 : CollatzResearch.WordTrace tailWord_846565 prefixEnd_846565 96598833394130120943161 := by
  unfold tailWord_846565
  simp only [CollatzResearch.WordTrace]
  refine ⟨30876762178047061636365149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20584508118698041090910099 30876762178047061636365149)
  ·
    refine ⟨11578785816767648113636931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30876762178047061636365149 11578785816767648113636931)
    ·
      refine ⟨17368178725151472170455397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11578785816767648113636931 17368178725151472170455397)
      ·
        refine ⟨3256533510965901031960387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17368178725151472170455397 3256533510965901031960387)
        ·
          refine ⟨4884800266448851547940581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3256533510965901031960387 4884800266448851547940581)
          ·
            refine ⟨915900049959159665238859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4884800266448851547940581 915900049959159665238859)
            ·
              refine ⟨1373850074938739497858289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915900049959159665238859 1373850074938739497858289)
              ·
                refine ⟨1030387556204054623393717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373850074938739497858289 1030387556204054623393717)
                ·
                  refine ⟨96598833394130120943161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1030387556204054623393717 96598833394130120943161)
                  ·
                    rfl

theorem cell22_846565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_846565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846565 prefixEnd_846565 := by exact prefixLift 846565
  have htrace : WordTrace (prefixWord ++ tailWord_846565) baseStart_846565 baseEnd_846565 := by
    simpa [prefixWord, tailWord_846565, baseEnd_846565] using wordTrace_append hprefix tailTrace_846565
  have hstable : (prefixWord ++ tailWord_846565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846565).length < 2 ^ (prefixWord ++ tailWord_846565).sum := by decide
  have hdescent : baseEnd_846565 < baseStart_846565 := by decide
  rcases family_descends (prefixWord ++ tailWord_846565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846623 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 4, 4]
def baseStart_846623 : Nat := 118140960795 + 846623 * 2 ^ 59
def prefixEnd_846623 : Nat := 4983230072969 + 3 ^ 40 * 846623 * 2
def baseEnd_846623 : Nat := 289816354767697544879305

theorem tailTrace_846623 : CollatzResearch.WordTrace tailWord_846623 prefixEnd_846623 289816354767697544879305 := by
  unfold tailWord_846623
  simp only [CollatzResearch.WordTrace]
  refine ⟨30878877611836937541976523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20585918407891291694651015 30878877611836937541976523)
  ·
    refine ⟨46318316417755406312964785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30878877611836937541976523 46318316417755406312964785)
    ·
      refine ⟨34738737313316554734723589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46318316417755406312964785 34738737313316554734723589)
      ·
        refine ⟨6513513246246854012760673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34738737313316554734723589 6513513246246854012760673)
        ·
          refine ⟨4885134934685140509570505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6513513246246854012760673 4885134934685140509570505)
          ·
            refine ⟨3663851201013855382177879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4885134934685140509570505 3663851201013855382177879)
            ·
              refine ⟨5495776801520783073266819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3663851201013855382177879 5495776801520783073266819)
              ·
                refine ⟨8243665202281174609900229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5495776801520783073266819 8243665202281174609900229)
                ·
                  refine ⟨1545687225427720239356293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8243665202281174609900229 1545687225427720239356293)
                  ·
                    refine ⟨289816354767697544879305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1545687225427720239356293 289816354767697544879305)
                    ·
                      rfl

theorem cell22_846623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_846623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846623 prefixEnd_846623 := by exact prefixLift 846623
  have htrace : WordTrace (prefixWord ++ tailWord_846623) baseStart_846623 baseEnd_846623 := by
    simpa [prefixWord, tailWord_846623, baseEnd_846623] using wordTrace_append hprefix tailTrace_846623
  have hstable : (prefixWord ++ tailWord_846623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846623).length < 2 ^ (prefixWord ++ tailWord_846623).sum := by decide
  have hdescent : baseEnd_846623 < baseStart_846623 := by decide
  rcases family_descends (prefixWord ++ tailWord_846623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846625 : List Nat := [1, 2, 3, 2, 1, 2, 2, 4, 2, 3]
def baseStart_846625 : Nat := 118140960795 + 846625 * 2 ^ 59
def prefixEnd_846625 : Nat := 4983230072969 + 3 ^ 40 * 846625 * 2
def baseEnd_846625 : Nat := 289817039408570206329299

theorem tailTrace_846625 : CollatzResearch.WordTrace tailWord_846625 prefixEnd_846625 289817039408570206329299 := by
  unfold tailWord_846625
  simp only [CollatzResearch.WordTrace]
  refine ⟨30878950557829691883549329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20585967038553127922366219 30878950557829691883549329)
  ·
    refine ⟨23159212918372268912661997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30878950557829691883549329 23159212918372268912661997)
    ·
      refine ⟨8684704844389600842248249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23159212918372268912661997 8684704844389600842248249)
      ·
        refine ⟨6513528633292200631686187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8684704844389600842248249 6513528633292200631686187)
        ·
          refine ⟨9770292949938300947529281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6513528633292200631686187 9770292949938300947529281)
          ·
            refine ⟨7327719712453725710646961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9770292949938300947529281 7327719712453725710646961)
            ·
              refine ⟨5495789784340294282985221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7327719712453725710646961 5495789784340294282985221)
              ·
                refine ⟨1030460584563805178059729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5495789784340294282985221 1030460584563805178059729)
                ·
                  refine ⟨772845438422853883544797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1030460584563805178059729 772845438422853883544797)
                  ·
                    refine ⟨289817039408570206329299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 772845438422853883544797 289817039408570206329299)
                    ·
                      rfl

theorem cell22_846625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_846625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846625 prefixEnd_846625 := by exact prefixLift 846625
  have htrace : WordTrace (prefixWord ++ tailWord_846625) baseStart_846625 baseEnd_846625 := by
    simpa [prefixWord, tailWord_846625, baseEnd_846625] using wordTrace_append hprefix tailTrace_846625
  have hstable : (prefixWord ++ tailWord_846625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846625).length < 2 ^ (prefixWord ++ tailWord_846625).sum := by decide
  have hdescent : baseEnd_846625 < baseStart_846625 := by decide
  rcases family_descends (prefixWord ++ tailWord_846625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846646 : List Nat := [5, 1, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_846646 : Nat := 118140960795 + 846646 * 2 ^ 59
def prefixEnd_846646 : Nat := 4983230072969 + 3 ^ 40 * 846646 * 2
def baseEnd_846646 : Nat := 289824228137733151554235

theorem tailTrace_846646 : CollatzResearch.WordTrace tailWord_846646 prefixEnd_846646 289824228137733151554235 := by
  unfold tailWord_846646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1929982280672100779378987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20586477660502408313375861 1929982280672100779378987)
  ·
    refine ⟨2894973421008151169068481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1929982280672100779378987 2894973421008151169068481)
    ·
      refine ⟨2171230065756113376801361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2894973421008151169068481 2171230065756113376801361)
      ·
        refine ⟨1628422549317085032601021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2171230065756113376801361 1628422549317085032601021)
        ·
          refine ⟨610658455993906887225383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1628422549317085032601021 610658455993906887225383)
          ·
            refine ⟨915987683990860330838075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610658455993906887225383 915987683990860330838075)
            ·
              refine ⟨1373981525986290496257113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915987683990860330838075 1373981525986290496257113)
              ·
                refine ⟨1030486144489717872192835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373981525986290496257113 1030486144489717872192835)
                ·
                  refine ⟨1545729216734576808289253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1030486144489717872192835 1545729216734576808289253)
                  ·
                    refine ⟨289824228137733151554235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1545729216734576808289253 289824228137733151554235)
                    ·
                      rfl

theorem cell22_846646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_846646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846646 prefixEnd_846646 := by exact prefixLift 846646
  have htrace : WordTrace (prefixWord ++ tailWord_846646) baseStart_846646 baseEnd_846646 := by
    simpa [prefixWord, tailWord_846646, baseEnd_846646] using wordTrace_append hprefix tailTrace_846646
  have hstable : (prefixWord ++ tailWord_846646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846646).length < 2 ^ (prefixWord ++ tailWord_846646).sum := by decide
  have hdescent : baseEnd_846646 < baseStart_846646 := by decide
  rcases family_descends (prefixWord ++ tailWord_846646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846687 : List Nat := [1, 1, 2, 3, 1, 3, 3, 4, 1, 3]
def baseStart_846687 : Nat := 118140960795 + 846687 * 2 ^ 59
def prefixEnd_846687 : Nat := 4983230072969 + 3 ^ 40 * 846687 * 2
def baseEnd_846687 : Nat := 289838263275622711279109

theorem tailTrace_846687 : CollatzResearch.WordTrace tailWord_846687 prefixEnd_846687 289838263275622711279109 := by
  unfold tailWord_846687
  simp only [CollatzResearch.WordTrace]
  refine ⟨30881211883605076472306315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20587474589070050981537543 30881211883605076472306315)
  ·
    refine ⟨46321817825407614708459473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30881211883605076472306315 46321817825407614708459473)
    ·
      refine ⟨34741363369055711031344605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46321817825407614708459473 34741363369055711031344605)
      ·
        refine ⟨13028011263395891636754227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34741363369055711031344605 13028011263395891636754227)
        ·
          refine ⟨19542016895093837455131341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13028011263395891636754227 19542016895093837455131341)
          ·
            refine ⟨7328256335660189045674253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19542016895093837455131341 7328256335660189045674253)
            ·
              refine ⟨2748096125872570892127845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7328256335660189045674253 2748096125872570892127845)
              ·
                refine ⟨515268023601107042273971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2748096125872570892127845 515268023601107042273971)
                ·
                  refine ⟨772902035401660563410957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515268023601107042273971 772902035401660563410957)
                  ·
                    refine ⟨289838263275622711279109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 772902035401660563410957 289838263275622711279109)
                    ·
                      rfl

theorem cell22_846687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 1, 3].length) (baseStart_846687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846687 prefixEnd_846687 := by exact prefixLift 846687
  have htrace : WordTrace (prefixWord ++ tailWord_846687) baseStart_846687 baseEnd_846687 := by
    simpa [prefixWord, tailWord_846687, baseEnd_846687] using wordTrace_append hprefix tailTrace_846687
  have hstable : (prefixWord ++ tailWord_846687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846687).length < 2 ^ (prefixWord ++ tailWord_846687).sum := by decide
  have hdescent : baseEnd_846687 < baseStart_846687 := by decide
  rcases family_descends (prefixWord ++ tailWord_846687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846792 : List Nat := [2, 1, 3, 1, 5, 1, 1, 2, 2, 4]
def baseStart_846792 : Nat := 118140960795 + 846792 * 2 ^ 59
def prefixEnd_846792 : Nat := 4983230072969 + 3 ^ 40 * 846792 * 2
def baseEnd_846792 : Nat := 289874206921437437403787

theorem tailTrace_846792 : CollatzResearch.WordTrace tailWord_846792 prefixEnd_846792 289874206921437437403787 := by
  unfold tailWord_846792
  simp only [CollatzResearch.WordTrace]
  refine ⟨15442520774112339702439315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20590027698816452936585753 15442520774112339702439315)
  ·
    refine ⟨23163781161168509553658973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15442520774112339702439315 23163781161168509553658973)
    ·
      refine ⟨8686417935438191082622115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23163781161168509553658973 8686417935438191082622115)
      ·
        refine ⟨13029626903157286623933173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8686417935438191082622115 13029626903157286623933173)
        ·
          refine ⟨1221527522170995620993735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13029626903157286623933173 1221527522170995620993735)
          ·
            refine ⟨1832291283256493431490603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221527522170995620993735 1832291283256493431490603)
            ·
              refine ⟨2748436924884740147235905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1832291283256493431490603 2748436924884740147235905)
              ·
                refine ⟨2061327693663555110426929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2748436924884740147235905 2061327693663555110426929)
                ·
                  refine ⟨1545995770247666332820197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2061327693663555110426929 1545995770247666332820197)
                  ·
                    refine ⟨289874206921437437403787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1545995770247666332820197 289874206921437437403787)
                    ·
                      rfl

theorem cell22_846792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_846792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846792 prefixEnd_846792 := by exact prefixLift 846792
  have htrace : WordTrace (prefixWord ++ tailWord_846792) baseStart_846792 baseEnd_846792 := by
    simpa [prefixWord, tailWord_846792, baseEnd_846792] using wordTrace_append hprefix tailTrace_846792
  have hstable : (prefixWord ++ tailWord_846792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846792).length < 2 ^ (prefixWord ++ tailWord_846792).sum := by decide
  have hdescent : baseEnd_846792 < baseStart_846792 := by decide
  rcases family_descends (prefixWord ++ tailWord_846792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846856 : List Nat := [2, 1, 3, 2, 1, 3, 4, 2, 1, 3]
def baseStart_846856 : Nat := 118140960795 + 846856 * 2 ^ 59
def prefixEnd_846856 : Nat := 4983230072969 + 3 ^ 40 * 846856 * 2
def baseEnd_846856 : Nat := 289896115429362603803591

theorem tailTrace_846856 : CollatzResearch.WordTrace tailWord_846856 prefixEnd_846856 289896115429362603803591 := by
  unfold tailWord_846856
  simp only [CollatzResearch.WordTrace]
  refine ⟨15443687909996409167604211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20591583879995212223472281 15443687909996409167604211)
  ·
    refine ⟨23165531864994613751406317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15443687909996409167604211 23165531864994613751406317)
    ·
      refine ⟨8687074449372980156777369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23165531864994613751406317 8687074449372980156777369)
      ·
        refine ⟨6515305837029735117583027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8687074449372980156777369 6515305837029735117583027)
        ·
          refine ⟨9772958755544602676374541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6515305837029735117583027 9772958755544602676374541)
          ·
            refine ⟨3664859533329226003640453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9772958755544602676374541 3664859533329226003640453)
            ·
              refine ⟨687161162499229875682585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3664859533329226003640453 687161162499229875682585)
              ·
                refine ⟨515370871874422406761939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 687161162499229875682585 515370871874422406761939)
                ·
                  refine ⟨773056307811633610142909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515370871874422406761939 773056307811633610142909)
                  ·
                    refine ⟨289896115429362603803591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 773056307811633610142909 289896115429362603803591)
                    ·
                      rfl

theorem cell22_846856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_846856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846856 prefixEnd_846856 := by exact prefixLift 846856
  have htrace : WordTrace (prefixWord ++ tailWord_846856) baseStart_846856 baseEnd_846856 := by
    simpa [prefixWord, tailWord_846856, baseEnd_846856] using wordTrace_append hprefix tailTrace_846856
  have hstable : (prefixWord ++ tailWord_846856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846856).length < 2 ^ (prefixWord ++ tailWord_846856).sum := by decide
  have hdescent : baseEnd_846856 < baseStart_846856 := by decide
  rcases family_descends (prefixWord ++ tailWord_846856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846882 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_846882 : Nat := 118140960795 + 846882 * 2 ^ 59
def prefixEnd_846882 : Nat := 4983230072969 + 3 ^ 40 * 846882 * 2
def baseEnd_846882 : Nat := 289905015760707202653511

theorem tailTrace_846882 : CollatzResearch.WordTrace tailWord_846882 prefixEnd_846882 289905015760707202653511 := by
  unfold tailWord_846882
  simp only [CollatzResearch.WordTrace]
  refine ⟨7722081029474656193913725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20592216078599083183769933 7722081029474656193913725)
  ·
    refine ⟨2895780386052996072717647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7722081029474656193913725 2895780386052996072717647)
    ·
      refine ⟨4343670579079494109076471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2895780386052996072717647 4343670579079494109076471)
      ·
        refine ⟨6515505868619241163614707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4343670579079494109076471 6515505868619241163614707)
        ·
          refine ⟨9773258802928861745422061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6515505868619241163614707 9773258802928861745422061)
          ·
            refine ⟨3664972051098323154533273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9773258802928861745422061 3664972051098323154533273)
            ·
              refine ⟨2748729038323742365899955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3664972051098323154533273 2748729038323742365899955)
              ·
                refine ⟨4123093557485613548849933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748729038323742365899955 4123093557485613548849933)
                ·
                  refine ⟨1546160084057105080818725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4123093557485613548849933 1546160084057105080818725)
                  ·
                    refine ⟨289905015760707202653511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1546160084057105080818725 289905015760707202653511)
                    ·
                      rfl

theorem cell22_846882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_846882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846882 prefixEnd_846882 := by exact prefixLift 846882
  have htrace : WordTrace (prefixWord ++ tailWord_846882) baseStart_846882 baseEnd_846882 := by
    simpa [prefixWord, tailWord_846882, baseEnd_846882] using wordTrace_append hprefix tailTrace_846882
  have hstable : (prefixWord ++ tailWord_846882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846882).length < 2 ^ (prefixWord ++ tailWord_846882).sum := by decide
  have hdescent : baseEnd_846882 < baseStart_846882 := by decide
  rcases family_descends (prefixWord ++ tailWord_846882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846912 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 4, 3]
def baseStart_846912 : Nat := 118140960795 + 846912 * 2 ^ 59
def prefixEnd_846912 : Nat := 4983230072969 + 3 ^ 40 * 846912 * 2
def baseEnd_846912 : Nat := 289915285373797124403419

theorem tailTrace_846912 : CollatzResearch.WordTrace tailWord_846912 prefixEnd_846912 289915285373797124403419 := by
  unfold tailWord_846912
  simp only [CollatzResearch.WordTrace]
  refine ⟨15444709153894969949623495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20592945538526626599497993 15444709153894969949623495)
  ·
    refine ⟨23167063730842454924435243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15444709153894969949623495 23167063730842454924435243)
    ·
      refine ⟨34750595596263682386652865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23167063730842454924435243 34750595596263682386652865)
      ·
        refine ⟨26062946697197761789989649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34750595596263682386652865 26062946697197761789989649)
        ·
          refine ⟨19547210022898321342492237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26062946697197761789989649 19547210022898321342492237)
          ·
            refine ⟨7330203758586870503434589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19547210022898321342492237 7330203758586870503434589)
            ·
              refine ⟨2748826409470076438787971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7330203758586870503434589 2748826409470076438787971)
              ·
                refine ⟨4123239614205114658181957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748826409470076438787971 4123239614205114658181957)
                ·
                  refine ⟨773107427663458998409117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4123239614205114658181957 773107427663458998409117)
                  ·
                    refine ⟨289915285373797124403419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 773107427663458998409117 289915285373797124403419)
                    ·
                      rfl

theorem cell22_846912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 4, 3].length) (baseStart_846912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_846912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_846912 prefixEnd_846912 := by exact prefixLift 846912
  have htrace : WordTrace (prefixWord ++ tailWord_846912) baseStart_846912 baseEnd_846912 := by
    simpa [prefixWord, tailWord_846912, baseEnd_846912] using wordTrace_append hprefix tailTrace_846912
  have hstable : (prefixWord ++ tailWord_846912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846912).length < 2 ^ (prefixWord ++ tailWord_846912).sum := by decide
  have hdescent : baseEnd_846912 < baseStart_846912 := by decide
  rcases family_descends (prefixWord ++ tailWord_846912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847021 : List Nat := [1, 5, 2, 1, 3, 1, 2, 2, 5]
def baseStart_847021 : Nat := 118140960795 + 847021 * 2 ^ 59
def prefixEnd_847021 : Nat := 4983230072969 + 3 ^ 40 * 847021 * 2
def baseEnd_847021 : Nat := 96650866100452391142695

theorem tailTrace_847021 : CollatzResearch.WordTrace tailWord_847021 prefixEnd_847021 96650866100452391142695 := by
  unfold tailWord_847021
  simp only [CollatzResearch.WordTrace]
  refine ⟨30893393864395051514964917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20595595909596701009976611 30893393864395051514964917)
  ·
    refine ⟨2896255674787036079527961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30893393864395051514964917 2896255674787036079527961)
    ·
      refine ⟨2172191756090277059645971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2896255674787036079527961 2172191756090277059645971)
      ·
        refine ⟨3258287634135415589468957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2172191756090277059645971 3258287634135415589468957)
        ·
          refine ⟨1221857862800780846050859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3258287634135415589468957 1221857862800780846050859)
          ·
            refine ⟨1832786794201171269076289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221857862800780846050859 1832786794201171269076289)
            ·
              refine ⟨1374590095650878451807217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1832786794201171269076289 1374590095650878451807217)
              ·
                refine ⟨1030942571738158838855413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1374590095650878451807217 1030942571738158838855413)
                ·
                  refine ⟨96650866100452391142695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1030942571738158838855413 96650866100452391142695)
                  ·
                    rfl

theorem cell22_847021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_847021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847021 prefixEnd_847021 := by exact prefixLift 847021
  have htrace : WordTrace (prefixWord ++ tailWord_847021) baseStart_847021 baseEnd_847021 := by
    simpa [prefixWord, tailWord_847021, baseEnd_847021] using wordTrace_append hprefix tailTrace_847021
  have hstable : (prefixWord ++ tailWord_847021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847021).length < 2 ^ (prefixWord ++ tailWord_847021).sum := by decide
  have hdescent : baseEnd_847021 < baseStart_847021 := by decide
  rcases family_descends (prefixWord ++ tailWord_847021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847025 : List Nat := [1, 2, 2, 5, 1, 3, 2, 2, 1, 3]
def baseStart_847025 : Nat := 118140960795 + 847025 * 2 ^ 59
def prefixEnd_847025 : Nat := 4983230072969 + 3 ^ 40 * 847025 * 2
def baseEnd_847025 : Nat := 289953967583102496328073

theorem tailTrace_847025 : CollatzResearch.WordTrace tailWord_847025 prefixEnd_847025 289953967583102496328073 := by
  unfold tailWord_847025
  simp only [CollatzResearch.WordTrace]
  refine ⟨30893539756380560198110529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20595693170920373465407019 30893539756380560198110529)
  ·
    refine ⟨23170154817285420148582897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30893539756380560198110529 23170154817285420148582897)
    ·
      refine ⟨17377616112964065111437173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23170154817285420148582897 17377616112964065111437173)
      ·
        refine ⟨1629151510590381104197235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17377616112964065111437173 1629151510590381104197235)
        ·
          refine ⟨2443727265885571656295853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1629151510590381104197235 2443727265885571656295853)
          ·
            refine ⟨916397724707089371110945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2443727265885571656295853 916397724707089371110945)
            ·
              refine ⟨687298293530317028333209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 916397724707089371110945 687298293530317028333209)
              ·
                refine ⟨515473720147737771249907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 687298293530317028333209 515473720147737771249907)
                ·
                  refine ⟨773210580221606656874861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515473720147737771249907 773210580221606656874861)
                  ·
                    refine ⟨289953967583102496328073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 773210580221606656874861 289953967583102496328073)
                    ·
                      rfl

theorem cell22_847025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 1, 3].length) (baseStart_847025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847025 prefixEnd_847025 := by exact prefixLift 847025
  have htrace : WordTrace (prefixWord ++ tailWord_847025) baseStart_847025 baseEnd_847025 := by
    simpa [prefixWord, tailWord_847025, baseEnd_847025] using wordTrace_append hprefix tailTrace_847025
  have hstable : (prefixWord ++ tailWord_847025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847025).length < 2 ^ (prefixWord ++ tailWord_847025).sum := by decide
  have hdescent : baseEnd_847025 < baseStart_847025 := by decide
  rcases family_descends (prefixWord ++ tailWord_847025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847109 : List Nat := [1, 3, 1, 1, 2, 1, 3, 4, 3, 3]
def baseStart_847109 : Nat := 118140960795 + 847109 * 2 ^ 59
def prefixEnd_847109 : Nat := 4983230072969 + 3 ^ 40 * 847109 * 2
def baseEnd_847109 : Nat := 289982722499754277227815

theorem tailTrace_847109 : CollatzResearch.WordTrace tailWord_847109 prefixEnd_847109 289982722499754277227815 := by
  unfold tailWord_847109
  simp only [CollatzResearch.WordTrace]
  refine ⟨30896603488076242544168381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20597735658717495029445587 30896603488076242544168381)
  ·
    refine ⟨11586226308028590954063143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30896603488076242544168381 11586226308028590954063143)
    ·
      refine ⟨17379339462042886431094715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11586226308028590954063143 17379339462042886431094715)
      ·
        refine ⟨26069009193064329646642073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17379339462042886431094715 26069009193064329646642073)
        ·
          refine ⟨19551756894798247234981555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26069009193064329646642073 19551756894798247234981555)
          ·
            refine ⟨29327635342197370852472333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19551756894798247234981555 29327635342197370852472333)
            ·
              refine ⟨10997863253324014069677125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29327635342197370852472333 10997863253324014069677125)
              ·
                refine ⟨2062099359998252638064461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10997863253324014069677125 2062099359998252638064461)
                ·
                  refine ⟨773287259999344739274173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2062099359998252638064461 773287259999344739274173)
                  ·
                    refine ⟨289982722499754277227815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 773287259999344739274173 289982722499754277227815)
                    ·
                      rfl

theorem cell22_847109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_847109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847109 prefixEnd_847109 := by exact prefixLift 847109
  have htrace : WordTrace (prefixWord ++ tailWord_847109) baseStart_847109 baseEnd_847109 := by
    simpa [prefixWord, tailWord_847109, baseEnd_847109] using wordTrace_append hprefix tailTrace_847109
  have hstable : (prefixWord ++ tailWord_847109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847109).length < 2 ^ (prefixWord ++ tailWord_847109).sum := by decide
  have hdescent : baseEnd_847109 < baseStart_847109 := by decide
  rcases family_descends (prefixWord ++ tailWord_847109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847156 : List Nat := [2, 5, 1, 1, 1, 1, 3, 3, 5]
def baseStart_847156 : Nat := 118140960795 + 847156 * 2 ^ 59
def prefixEnd_847156 : Nat := 4983230072969 + 3 ^ 40 * 847156 * 2
def baseEnd_847156 : Nat := 96666270520087273767557

theorem tailTrace_847156 : CollatzResearch.WordTrace tailWord_847156 prefixEnd_847156 96666270520087273767557 := by
  unfold tailWord_847156
  simp only [CollatzResearch.WordTrace]
  refine ⟨15449158859452984785564661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20598878479270646380752881 15449158859452984785564661)
  ·
    refine ⟨1448358643073717323646687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15449158859452984785564661 1448358643073717323646687)
    ·
      refine ⟨2172537964610575985470031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1448358643073717323646687 2172537964610575985470031)
      ·
        refine ⟨3258806946915863978205047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2172537964610575985470031 3258806946915863978205047)
        ·
          refine ⟨4888210420373795967307571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3258806946915863978205047 4888210420373795967307571)
          ·
            refine ⟨7332315630560693950961357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4888210420373795967307571 7332315630560693950961357)
            ·
              refine ⟨2749618361460260231610509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7332315630560693950961357 2749618361460260231610509)
              ·
                refine ⟨1031106885547597586853941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2749618361460260231610509 1031106885547597586853941)
                ·
                  refine ⟨96666270520087273767557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1031106885547597586853941 96666270520087273767557)
                  ·
                    rfl

theorem cell22_847156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_847156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847156 prefixEnd_847156 := by exact prefixLift 847156
  have htrace : WordTrace (prefixWord ++ tailWord_847156) baseStart_847156 baseEnd_847156 := by
    simpa [prefixWord, tailWord_847156, baseEnd_847156] using wordTrace_append hprefix tailTrace_847156
  have hstable : (prefixWord ++ tailWord_847156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847156).length < 2 ^ (prefixWord ++ tailWord_847156).sum := by decide
  have hdescent : baseEnd_847156 < baseStart_847156 := by decide
  rcases family_descends (prefixWord ++ tailWord_847156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847216 : List Nat := [2, 1, 1, 1, 4, 2, 1, 5, 2, 3]
def baseStart_847216 : Nat := 118140960795 + 847216 * 2 ^ 59
def prefixEnd_847216 : Nat := 4983230072969 + 3 ^ 40 * 847216 * 2
def baseEnd_847216 : Nat := 290019350786441664802487

theorem tailTrace_847216 : CollatzResearch.WordTrace tailWord_847216 prefixEnd_847216 290019350786441664802487 := by
  unfold tailWord_847216
  simp only [CollatzResearch.WordTrace]
  refine ⟨15450253049344299909156751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20600337399125733212209001 15450253049344299909156751)
  ·
    refine ⟨23175379574016449863735127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15450253049344299909156751 23175379574016449863735127)
    ·
      refine ⟨34763069361024674795602691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23175379574016449863735127 34763069361024674795602691)
      ·
        refine ⟨52144604041537012193404037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34763069361024674795602691 52144604041537012193404037)
        ·
          refine ⟨9777113257788189786263257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52144604041537012193404037 9777113257788189786263257)
          ·
            refine ⟨7332834943341142339697443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9777113257788189786263257 7332834943341142339697443)
            ·
              refine ⟨10999252415011713509546165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7332834943341142339697443 10999252415011713509546165)
              ·
                refine ⟨1031179913907348141519953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10999252415011713509546165 1031179913907348141519953)
                ·
                  refine ⟨773384935430511106139965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1031179913907348141519953 773384935430511106139965)
                  ·
                    refine ⟨290019350786441664802487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 773384935430511106139965 290019350786441664802487)
                    ·
                      rfl

theorem cell22_847216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 2, 3].length) (baseStart_847216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847216 prefixEnd_847216 := by exact prefixLift 847216
  have htrace : WordTrace (prefixWord ++ tailWord_847216) baseStart_847216 baseEnd_847216 := by
    simpa [prefixWord, tailWord_847216, baseEnd_847216] using wordTrace_append hprefix tailTrace_847216
  have hstable : (prefixWord ++ tailWord_847216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847216).length < 2 ^ (prefixWord ++ tailWord_847216).sum := by decide
  have hdescent : baseEnd_847216 < baseStart_847216 := by decide
  rcases family_descends (prefixWord ++ tailWord_847216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847246 : List Nat := [4, 1, 1, 4, 2, 1, 9]
def baseStart_847246 : Nat := 118140960795 + 847246 * 2 ^ 59
def prefixEnd_847246 : Nat := 4983230072969 + 3 ^ 40 * 847246 * 2
def baseEnd_847246 : Nat := 10741837792575243946385

theorem tailTrace_847246 : CollatzResearch.WordTrace tailWord_847246 prefixEnd_847246 10741837792575243946385 := by
  unfold tailWord_847246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3862700036072489367738199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20601066859053276627937061 3862700036072489367738199)
  ·
    refine ⟨5794050054108734051607299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3862700036072489367738199 5794050054108734051607299)
    ·
      refine ⟨8691075081163101077410949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5794050054108734051607299 8691075081163101077410949)
      ·
        refine ⟨1629576577718081452014553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8691075081163101077410949 1629576577718081452014553)
        ·
          refine ⟨1222182433288561089010915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1629576577718081452014553 1222182433288561089010915)
          ·
            refine ⟨1833273649932841633516373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222182433288561089010915 1833273649932841633516373)
            ·
              refine ⟨10741837792575243946385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1833273649932841633516373 10741837792575243946385)
              ·
                rfl

theorem cell22_847246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 9].length) (baseStart_847246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847246 prefixEnd_847246 := by exact prefixLift 847246
  have htrace : WordTrace (prefixWord ++ tailWord_847246) baseStart_847246 baseEnd_847246 := by
    simpa [prefixWord, tailWord_847246, baseEnd_847246] using wordTrace_append hprefix tailTrace_847246
  have hstable : (prefixWord ++ tailWord_847246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847246).length < 2 ^ (prefixWord ++ tailWord_847246).sum := by decide
  have hdescent : baseEnd_847246 < baseStart_847246 := by decide
  rcases family_descends (prefixWord ++ tailWord_847246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847250 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 4, 3]
def baseStart_847250 : Nat := 118140960795 + 847250 * 2 ^ 59
def prefixEnd_847250 : Nat := 4983230072969 + 3 ^ 40 * 847250 * 2
def baseEnd_847250 : Nat := 290030989681276909452383

theorem tailTrace_847250 : CollatzResearch.WordTrace tailWord_847250 prefixEnd_847250 290030989681276909452383 := by
  unfold tailWord_847250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7725436545141355906262801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20601164120376949083367469 7725436545141355906262801)
  ·
    refine ⟨5794077408856016929697101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7725436545141355906262801 5794077408856016929697101)
    ·
      refine ⟨2172779028321006348636413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5794077408856016929697101 2172779028321006348636413)
      ·
        refine ⟨814792135620377380738655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2172779028321006348636413 814792135620377380738655)
        ·
          refine ⟨1222188203430566071107983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814792135620377380738655 1222188203430566071107983)
          ·
            refine ⟨1833282305145849106661975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222188203430566071107983 1833282305145849106661975)
            ·
              refine ⟨2749923457718773659992963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1833282305145849106661975 2749923457718773659992963)
              ·
                refine ⟨4124885186578160489989445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2749923457718773659992963 4124885186578160489989445)
                ·
                  refine ⟨773415972483405091873021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4124885186578160489989445 773415972483405091873021)
                  ·
                    refine ⟨290030989681276909452383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 773415972483405091873021 290030989681276909452383)
                    ·
                      rfl

theorem cell22_847250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_847250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847250 prefixEnd_847250 := by exact prefixLift 847250
  have htrace : WordTrace (prefixWord ++ tailWord_847250) baseStart_847250 baseEnd_847250 := by
    simpa [prefixWord, tailWord_847250, baseEnd_847250] using wordTrace_append hprefix tailTrace_847250
  have hstable : (prefixWord ++ tailWord_847250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847250).length < 2 ^ (prefixWord ++ tailWord_847250).sum := by decide
  have hdescent : baseEnd_847250 < baseStart_847250 := by decide
  rcases family_descends (prefixWord ++ tailWord_847250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847325 : List Nat := [1, 4, 3, 1, 1, 4, 2, 1, 5]
def baseStart_847325 : Nat := 118140960795 + 847325 * 2 ^ 59
def prefixEnd_847325 : Nat := 4983230072969 + 3 ^ 40 * 847325 * 2
def baseEnd_847325 : Nat := 96685554571333904609051

theorem tailTrace_847325 : CollatzResearch.WordTrace tailWord_847325 prefixEnd_847325 96685554571333904609051 := by
  unfold tailWord_847325
  simp only [CollatzResearch.WordTrace]
  refine ⟨30904481655293711434031429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20602987770195807622687619 30904481655293711434031429)
  ·
    refine ⟨5794590310367570893880893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30904481655293711434031429 5794590310367570893880893)
    ·
      refine ⟨2172971366387839085205335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5794590310367570893880893 2172971366387839085205335)
      ·
        refine ⟨3259457049581758627808003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2172971366387839085205335 3259457049581758627808003)
        ·
          refine ⟨4889185574372637941712005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3259457049581758627808003 4889185574372637941712005)
          ·
            refine ⟨916722295194869614071001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4889185574372637941712005 916722295194869614071001)
            ·
              refine ⟨687541721396152210553251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 916722295194869614071001 687541721396152210553251)
              ·
                refine ⟨1031312582094228315829877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687541721396152210553251 1031312582094228315829877)
                ·
                  refine ⟨96685554571333904609051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1031312582094228315829877 96685554571333904609051)
                  ·
                    rfl

theorem cell22_847325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_847325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847325 prefixEnd_847325 := by exact prefixLift 847325
  have htrace : WordTrace (prefixWord ++ tailWord_847325) baseStart_847325 baseEnd_847325 := by
    simpa [prefixWord, tailWord_847325, baseEnd_847325] using wordTrace_append hprefix tailTrace_847325
  have hstable : (prefixWord ++ tailWord_847325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847325).length < 2 ^ (prefixWord ++ tailWord_847325).sum := by decide
  have hdescent : baseEnd_847325 < baseStart_847325 := by decide
  rcases family_descends (prefixWord ++ tailWord_847325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847338 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 3, 4]
def baseStart_847338 : Nat := 118140960795 + 847338 * 2 ^ 59
def prefixEnd_847338 : Nat := 4983230072969 + 3 ^ 40 * 847338 * 2
def baseEnd_847338 : Nat := 290061113879674013252113

theorem tailTrace_847338 : CollatzResearch.WordTrace tailWord_847338 prefixEnd_847338 290061113879674013252113 := by
  unfold tailWord_847338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7726238951061653663563667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20603303869497743102836445 7726238951061653663563667)
  ·
    refine ⟨11589358426592480495345501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7726238951061653663563667 11589358426592480495345501)
    ·
      refine ⟨4346009409972180185754563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11589358426592480495345501 4346009409972180185754563)
      ·
        refine ⟨6519014114958270278631845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4346009409972180185754563 6519014114958270278631845)
        ·
          refine ⟨1222315146554675677243471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6519014114958270278631845 1222315146554675677243471)
          ·
            refine ⟨1833472719832013515865207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222315146554675677243471 1833472719832013515865207)
            ·
              refine ⟨2750209079748020273797811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1833472719832013515865207 2750209079748020273797811)
              ·
                refine ⟨4125313619622030410696717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750209079748020273797811 4125313619622030410696717)
                ·
                  refine ⟨1546992607358261404011269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4125313619622030410696717 1546992607358261404011269)
                  ·
                    refine ⟨290061113879674013252113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1546992607358261404011269 290061113879674013252113)
                    ·
                      rfl

theorem cell22_847338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_847338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847338 prefixEnd_847338 := by exact prefixLift 847338
  have htrace : WordTrace (prefixWord ++ tailWord_847338) baseStart_847338 baseEnd_847338 := by
    simpa [prefixWord, tailWord_847338, baseEnd_847338] using wordTrace_append hprefix tailTrace_847338
  have hstable : (prefixWord ++ tailWord_847338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847338).length < 2 ^ (prefixWord ++ tailWord_847338).sum := by decide
  have hdescent : baseEnd_847338 < baseStart_847338 := by decide
  rcases family_descends (prefixWord ++ tailWord_847338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847351 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 4, 3]
def baseStart_847351 : Nat := 118140960795 + 847351 * 2 ^ 59
def prefixEnd_847351 : Nat := 4983230072969 + 3 ^ 40 * 847351 * 2
def baseEnd_847351 : Nat := 290065564045346312677073

theorem tailTrace_847351 : CollatzResearch.WordTrace tailWord_847351 prefixEnd_847351 290065564045346312677073 := by
  unfold tailWord_847351
  simp only [CollatzResearch.WordTrace]
  refine ⟨30905429953199517874477907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20603619968799678582985271 30905429953199517874477907)
  ·
    refine ⟨46358144929799276811716861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30905429953199517874477907 46358144929799276811716861)
    ·
      refine ⟨17384304348674728804393823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46358144929799276811716861 17384304348674728804393823)
      ·
        refine ⟨26076456523012093206590735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17384304348674728804393823 26076456523012093206590735)
        ·
          refine ⟨39114684784518139809886103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26076456523012093206590735 39114684784518139809886103)
          ·
            refine ⟨58672027176777209714829155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39114684784518139809886103 58672027176777209714829155)
            ·
              refine ⟨88008040765165814572243733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58672027176777209714829155 88008040765165814572243733)
              ·
                refine ⟨4125376910867147558073925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88008040765165814572243733 4125376910867147558073925)
                ·
                  refine ⟨773508170787590167138861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4125376910867147558073925 773508170787590167138861)
                  ·
                    refine ⟨290065564045346312677073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 773508170787590167138861 290065564045346312677073)
                    ·
                      rfl

theorem cell22_847351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_847351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847351 prefixEnd_847351 := by exact prefixLift 847351
  have htrace : WordTrace (prefixWord ++ tailWord_847351) baseStart_847351 baseEnd_847351 := by
    simpa [prefixWord, tailWord_847351, baseEnd_847351] using wordTrace_append hprefix tailTrace_847351
  have hstable : (prefixWord ++ tailWord_847351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847351).length < 2 ^ (prefixWord ++ tailWord_847351).sum := by decide
  have hdescent : baseEnd_847351 < baseStart_847351 := by decide
  rcases family_descends (prefixWord ++ tailWord_847351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847368 : List Nat := [2, 1, 3, 2, 1, 1, 3, 4, 2, 3]
def baseStart_847368 : Nat := 118140960795 + 847368 * 2 ^ 59
def prefixEnd_847368 : Nat := 4983230072969 + 3 ^ 40 * 847368 * 2
def baseEnd_847368 : Nat := 290071383492763935002021

theorem tailTrace_847368 : CollatzResearch.WordTrace tailWord_847368 prefixEnd_847368 290071383492763935002021 := by
  unfold tailWord_847368
  simp only [CollatzResearch.WordTrace]
  refine ⟨15453024997068964888923379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20604033329425286518564505 15453024997068964888923379)
  ·
    refine ⟨23179537495603447333385069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15453024997068964888923379 23179537495603447333385069)
    ·
      refine ⟨8692326560851292750019401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23179537495603447333385069 8692326560851292750019401)
      ·
        refine ⟨6519244920638469562514551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8692326560851292750019401 6519244920638469562514551)
        ·
          refine ⟨9778867380957704343771827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6519244920638469562514551 9778867380957704343771827)
          ·
            refine ⟨14668301071436556515657741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9778867380957704343771827 14668301071436556515657741)
            ·
              refine ⟨5500612901788708693371653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14668301071436556515657741 5500612901788708693371653)
              ·
                refine ⟨1031364919085382880007185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5500612901788708693371653 1031364919085382880007185)
                ·
                  refine ⟨773523689314037160005389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1031364919085382880007185 773523689314037160005389)
                  ·
                    refine ⟨290071383492763935002021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 773523689314037160005389 290071383492763935002021)
                    ·
                      rfl

theorem cell22_847368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_847368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847368 prefixEnd_847368 := by exact prefixLift 847368
  have htrace : WordTrace (prefixWord ++ tailWord_847368) baseStart_847368 baseEnd_847368 := by
    simpa [prefixWord, tailWord_847368, baseEnd_847368] using wordTrace_append hprefix tailTrace_847368
  have hstable : (prefixWord ++ tailWord_847368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847368).length < 2 ^ (prefixWord ++ tailWord_847368).sum := by decide
  have hdescent : baseEnd_847368 < baseStart_847368 := by decide
  rcases family_descends (prefixWord ++ tailWord_847368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847370 : List Nat := [3, 1, 2, 2, 2, 2, 4, 2, 4]
def baseStart_847370 : Nat := 118140960795 + 847370 * 2 ^ 59
def prefixEnd_847370 : Nat := 4983230072969 + 3 ^ 40 * 847370 * 2
def baseEnd_847370 : Nat := 96690689377878865484005

theorem tailTrace_847370 : CollatzResearch.WordTrace tailWord_847370 prefixEnd_847370 96690689377878865484005 := by
  unfold tailWord_847370
  simp only [CollatzResearch.WordTrace]
  refine ⟨7726530735032671029854891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20604081960087122746279709 7726530735032671029854891)
  ·
    refine ⟨11589796102549006544782337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7726530735032671029854891 11589796102549006544782337)
    ·
      refine ⟨8692347076911754908586753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11589796102549006544782337 8692347076911754908586753)
      ·
        refine ⟨6519260307683816181440065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8692347076911754908586753 6519260307683816181440065)
        ·
          refine ⟨4889445230762862136080049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6519260307683816181440065 4889445230762862136080049)
          ·
            refine ⟨3667083923072146602060037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4889445230762862136080049 3667083923072146602060037)
            ·
              refine ⟨687578235576027487886257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3667083923072146602060037 687578235576027487886257)
              ·
                refine ⟨515683676682020615914693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 687578235576027487886257 515683676682020615914693)
                ·
                  refine ⟨96690689377878865484005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 515683676682020615914693 96690689377878865484005)
                  ·
                    rfl

theorem cell22_847370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_847370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847370 prefixEnd_847370 := by exact prefixLift 847370
  have htrace : WordTrace (prefixWord ++ tailWord_847370) baseStart_847370 baseEnd_847370 := by
    simpa [prefixWord, tailWord_847370, baseEnd_847370] using wordTrace_append hprefix tailTrace_847370
  have hstable : (prefixWord ++ tailWord_847370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847370).length < 2 ^ (prefixWord ++ tailWord_847370).sum := by decide
  have hdescent : baseEnd_847370 < baseStart_847370 := by decide
  rcases family_descends (prefixWord ++ tailWord_847370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847381 : List Nat := [1, 3, 2, 1, 3, 2, 3, 7]
def baseStart_847381 : Nat := 118140960795 + 847381 * 2 ^ 59
def prefixEnd_847381 : Nat := 4983230072969 + 3 ^ 40 * 847381 * 2
def baseEnd_847381 : Nat := 32230648184270692714109

theorem tailTrace_847381 : CollatzResearch.WordTrace tailWord_847381 prefixEnd_847381 32230648184270692714109 := by
  unfold tailWord_847381
  simp only [CollatzResearch.WordTrace]
  refine ⟨30906524143090832998069997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20604349428727221998713331 30906524143090832998069997)
  ·
    refine ⟨11589946553659062374276249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30906524143090832998069997 11589946553659062374276249)
    ·
      refine ⟨8692459915244296780707187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11589946553659062374276249 8692459915244296780707187)
      ·
        refine ⟨13038689872866445171060781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8692459915244296780707187 13038689872866445171060781)
        ·
          refine ⟨4889508702324916939147793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13038689872866445171060781 4889508702324916939147793)
          ·
            refine ⟨3667131526743687704360845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4889508702324916939147793 3667131526743687704360845)
            ·
              refine ⟨1375174322528882889135317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3667131526743687704360845 1375174322528882889135317)
              ·
                refine ⟨32230648184270692714109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1375174322528882889135317 32230648184270692714109)
                ·
                  rfl

theorem cell22_847381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 7].length) (baseStart_847381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847381 prefixEnd_847381 := by exact prefixLift 847381
  have htrace : WordTrace (prefixWord ++ tailWord_847381) baseStart_847381 baseEnd_847381 := by
    simpa [prefixWord, tailWord_847381, baseEnd_847381] using wordTrace_append hprefix tailTrace_847381
  have hstable : (prefixWord ++ tailWord_847381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847381).length < 2 ^ (prefixWord ++ tailWord_847381).sum := by decide
  have hdescent : baseEnd_847381 < baseStart_847381 := by decide
  rcases family_descends (prefixWord ++ tailWord_847381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847441 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 2, 5]
def baseStart_847441 : Nat := 118140960795 + 847441 * 2 ^ 59
def prefixEnd_847441 : Nat := 4983230072969 + 3 ^ 40 * 847441 * 2
def baseEnd_847441 : Nat := 290096372884616077926797

theorem tailTrace_847441 : CollatzResearch.WordTrace tailWord_847441 prefixEnd_847441 290096372884616077926797 := by
  unfold tailWord_847441
  simp only [CollatzResearch.WordTrace]
  refine ⟨30908712522873463245254177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20605808348582308830169451 30908712522873463245254177)
  ·
    refine ⟨23181534392155097433940633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30908712522873463245254177 23181534392155097433940633)
    ·
      refine ⟨17386150794116323075455475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23181534392155097433940633 17386150794116323075455475)
      ·
        refine ⟨26079226191174484613183213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17386150794116323075455475 26079226191174484613183213)
        ·
          refine ⟨9779709821690431729943705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26079226191174484613183213 9779709821690431729943705)
          ·
            refine ⟨7334782366267823797457779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9779709821690431729943705 7334782366267823797457779)
            ·
              refine ⟨11002173549401735696186669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7334782366267823797457779 11002173549401735696186669)
              ·
                refine ⟨4125815081025650886070001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11002173549401735696186669 4125815081025650886070001)
                ·
                  refine ⟨3094361310769238164552501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4125815081025650886070001 3094361310769238164552501)
                  ·
                    refine ⟨290096372884616077926797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3094361310769238164552501 290096372884616077926797)
                    ·
                      rfl

theorem cell22_847441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_847441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847441 prefixEnd_847441 := by exact prefixLift 847441
  have htrace : WordTrace (prefixWord ++ tailWord_847441) baseStart_847441 baseEnd_847441 := by
    simpa [prefixWord, tailWord_847441, baseEnd_847441] using wordTrace_append hprefix tailTrace_847441
  have hstable : (prefixWord ++ tailWord_847441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847441).length < 2 ^ (prefixWord ++ tailWord_847441).sum := by decide
  have hdescent : baseEnd_847441 < baseStart_847441 := by decide
  rcases family_descends (prefixWord ++ tailWord_847441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847464 : List Nat := [2, 1, 4, 3, 1, 3, 1, 3, 1, 3]
def baseStart_847464 : Nat := 118140960795 + 847464 * 2 ^ 59
def prefixEnd_847464 : Nat := 4983230072969 + 3 ^ 40 * 847464 * 2
def baseEnd_847464 : Nat := 290104246254651684601727

theorem tailTrace_847464 : CollatzResearch.WordTrace tailWord_847464 prefixEnd_847464 290104246254651684601727 := by
  unfold tailWord_847464
  simp only [CollatzResearch.WordTrace]
  refine ⟨15454775700895069086670723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20606367601193425448894297 15454775700895069086670723)
  ·
    refine ⟨23182163551342603630006085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15454775700895069086670723 23182163551342603630006085)
    ·
      refine ⟨4346655665876738180626141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23182163551342603630006085 4346655665876738180626141)
      ·
        refine ⟨1629995874703776817734803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4346655665876738180626141 1629995874703776817734803)
        ·
          refine ⟨2444993812055665226602205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1629995874703776817734803 2444993812055665226602205)
          ·
            refine ⟨916872679520874459975827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2444993812055665226602205 916872679520874459975827)
            ·
              refine ⟨1375309019281311689963741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 916872679520874459975827 1375309019281311689963741)
              ·
                refine ⟨515740882230491883736403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1375309019281311689963741 515740882230491883736403)
                ·
                  refine ⟨773611323345737825604605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515740882230491883736403 773611323345737825604605)
                  ·
                    refine ⟨290104246254651684601727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 773611323345737825604605 290104246254651684601727)
                    ·
                      rfl

theorem cell22_847464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_847464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847464 prefixEnd_847464 := by exact prefixLift 847464
  have htrace : WordTrace (prefixWord ++ tailWord_847464) baseStart_847464 baseEnd_847464 := by
    simpa [prefixWord, tailWord_847464, baseEnd_847464] using wordTrace_append hprefix tailTrace_847464
  have hstable : (prefixWord ++ tailWord_847464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847464).length < 2 ^ (prefixWord ++ tailWord_847464).sum := by decide
  have hdescent : baseEnd_847464 < baseStart_847464 := by decide
  rcases family_descends (prefixWord ++ tailWord_847464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847550 : List Nat := [4, 2, 1, 1, 2, 4, 1, 7]
def baseStart_847550 : Nat := 118140960795 + 847550 * 2 ^ 59
def prefixEnd_847550 : Nat := 4983230072969 + 3 ^ 40 * 847550 * 2
def baseEnd_847550 : Nat := 32237076201352902994607

theorem tailTrace_847550 : CollatzResearch.WordTrace tailWord_847550 prefixEnd_847550 32237076201352902994607 := by
  unfold tailWord_847550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3864086009934821857621513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20608458719652383240648069 3864086009934821857621513)
  ·
    refine ⟨2898064507451116393216135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3864086009934821857621513 2898064507451116393216135)
    ·
      refine ⟨4347096761176674589824203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2898064507451116393216135 4347096761176674589824203)
      ·
        refine ⟨6520645141765011884736305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4347096761176674589824203 6520645141765011884736305)
        ·
          refine ⟨4890483856323758913552229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6520645141765011884736305 4890483856323758913552229)
          ·
            refine ⟨916965723060704796291043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4890483856323758913552229 916965723060704796291043)
            ·
              refine ⟨1375448584591057194436565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 916965723060704796291043 1375448584591057194436565)
              ·
                refine ⟨32237076201352902994607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1375448584591057194436565 32237076201352902994607)
                ·
                  rfl

theorem cell22_847550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_847550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847550 prefixEnd_847550 := by exact prefixLift 847550
  have htrace : WordTrace (prefixWord ++ tailWord_847550) baseStart_847550 baseEnd_847550 := by
    simpa [prefixWord, tailWord_847550, baseEnd_847550] using wordTrace_append hprefix tailTrace_847550
  have hstable : (prefixWord ++ tailWord_847550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847550).length < 2 ^ (prefixWord ++ tailWord_847550).sum := by decide
  have hdescent : baseEnd_847550 < baseStart_847550 := by decide
  rcases family_descends (prefixWord ++ tailWord_847550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847608 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 3, 4]
def baseStart_847608 : Nat := 118140960795 + 847608 * 2 ^ 59
def prefixEnd_847608 : Nat := 4983230072969 + 3 ^ 40 * 847608 * 2
def baseEnd_847608 : Nat := 290153540397483309001285

theorem tailTrace_847608 : CollatzResearch.WordTrace tailWord_847608 prefixEnd_847608 290153540397483309001285 := by
  unfold tailWord_847608
  simp only [CollatzResearch.WordTrace]
  refine ⟨15457401756634225383291739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20609869008845633844388985 15457401756634225383291739)
  ·
    refine ⟨23186102634951338074937609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15457401756634225383291739 23186102634951338074937609)
    ·
      refine ⟨17389576976213503556203207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23186102634951338074937609 17389576976213503556203207)
      ·
        refine ⟨26084365464320255334304811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17389576976213503556203207 26084365464320255334304811)
        ·
          refine ⟨39126548196480383001457217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26084365464320255334304811 39126548196480383001457217)
          ·
            refine ⟨29344911147360287251092913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39126548196480383001457217 29344911147360287251092913)
            ·
              refine ⟨22008683360520215438319685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29344911147360287251092913 22008683360520215438319685)
              ·
                refine ⟨4126628130097540394684941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22008683360520215438319685 4126628130097540394684941)
                ·
                  refine ⟨1547485548786577648006853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4126628130097540394684941 1547485548786577648006853)
                  ·
                    refine ⟨290153540397483309001285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1547485548786577648006853 290153540397483309001285)
                    ·
                      rfl

theorem cell22_847608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_847608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847608 prefixEnd_847608 := by exact prefixLift 847608
  have htrace : WordTrace (prefixWord ++ tailWord_847608) baseStart_847608 baseEnd_847608 := by
    simpa [prefixWord, tailWord_847608, baseEnd_847608] using wordTrace_append hprefix tailTrace_847608
  have hstable : (prefixWord ++ tailWord_847608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847608).length < 2 ^ (prefixWord ++ tailWord_847608).sum := by decide
  have hdescent : baseEnd_847608 < baseStart_847608 := by decide
  rcases family_descends (prefixWord ++ tailWord_847608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847672 : List Nat := [2, 1, 2, 1, 3, 4, 1, 3, 2, 3]
def baseStart_847672 : Nat := 118140960795 + 847672 * 2 ^ 59
def prefixEnd_847672 : Nat := 4983230072969 + 3 ^ 40 * 847672 * 2
def baseEnd_847672 : Nat := 290175448905408475401089

theorem tailTrace_847672 : CollatzResearch.WordTrace tailWord_847672 prefixEnd_847672 290175448905408475401089 := by
  unfold tailWord_847672
  simp only [CollatzResearch.WordTrace]
  refine ⟨15458568892518294848456635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20611425190024393131275513 15458568892518294848456635)
  ·
    refine ⟨23187853338777442272684953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15458568892518294848456635 23187853338777442272684953)
    ·
      refine ⟨17390890004083081704513715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23187853338777442272684953 17390890004083081704513715)
      ·
        refine ⟨26086335006124622556770573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17390890004083081704513715 26086335006124622556770573)
        ·
          refine ⟨9782375627296733458788965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26086335006124622556770573 9782375627296733458788965)
          ·
            refine ⟨1834195430118137523522931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9782375627296733458788965 1834195430118137523522931)
            ·
              refine ⟨2751293145177206285284397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1834195430118137523522931 2751293145177206285284397)
              ·
                refine ⟨1031734929441452356981649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2751293145177206285284397 1031734929441452356981649)
                ·
                  refine ⟨773801197081089267736237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1031734929441452356981649 773801197081089267736237)
                  ·
                    refine ⟨290175448905408475401089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 773801197081089267736237 290175448905408475401089)
                    ·
                      rfl

theorem cell22_847672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_847672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847672 prefixEnd_847672 := by exact prefixLift 847672
  have htrace : WordTrace (prefixWord ++ tailWord_847672) baseStart_847672 baseEnd_847672 := by
    simpa [prefixWord, tailWord_847672, baseEnd_847672] using wordTrace_append hprefix tailTrace_847672
  have hstable : (prefixWord ++ tailWord_847672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847672).length < 2 ^ (prefixWord ++ tailWord_847672).sum := by decide
  have hdescent : baseEnd_847672 < baseStart_847672 := by decide
  rcases family_descends (prefixWord ++ tailWord_847672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847708 : List Nat := [2, 2, 4, 2, 3, 1, 2, 2, 4]
def baseStart_847708 : Nat := 118140960795 + 847708 * 2 ^ 59
def prefixEnd_847708 : Nat := 4983230072969 + 3 ^ 40 * 847708 * 2
def baseEnd_847708 : Nat := 96729257480372127166993

theorem tailTrace_847708 : CollatzResearch.WordTrace tailWord_847708 prefixEnd_847708 96729257480372127166993 := by
  unfold tailWord_847708
  simp only [CollatzResearch.WordTrace]
  refine ⟨15459225406453083922611889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20612300541937445230149185 15459225406453083922611889)
  ·
    refine ⟨11594419054839812941958917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15459225406453083922611889 11594419054839812941958917)
    ·
      refine ⟨2173953572782464926617297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11594419054839812941958917 2173953572782464926617297)
      ·
        refine ⟨1630465179586848694962973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2173953572782464926617297 1630465179586848694962973)
        ·
          refine ⟨611424442345068260611115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1630465179586848694962973 611424442345068260611115)
          ·
            refine ⟨917136663517602390916673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611424442345068260611115 917136663517602390916673)
            ·
              refine ⟨687852497638201793187505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 917136663517602390916673 687852497638201793187505)
              ·
                refine ⟨515889373228651344890629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 687852497638201793187505 515889373228651344890629)
                ·
                  refine ⟨96729257480372127166993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 515889373228651344890629 96729257480372127166993)
                  ·
                    rfl

theorem cell22_847708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_847708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847708 prefixEnd_847708 := by exact prefixLift 847708
  have htrace : WordTrace (prefixWord ++ tailWord_847708) baseStart_847708 baseEnd_847708 := by
    simpa [prefixWord, tailWord_847708, baseEnd_847708] using wordTrace_append hprefix tailTrace_847708
  have hstable : (prefixWord ++ tailWord_847708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847708).length < 2 ^ (prefixWord ++ tailWord_847708).sum := by decide
  have hdescent : baseEnd_847708 < baseStart_847708 := by decide
  rcases family_descends (prefixWord ++ tailWord_847708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847751 : List Nat := [1, 1, 4, 2, 4, 1, 2, 3, 1, 3]
def baseStart_847751 : Nat := 118140960795 + 847751 * 2 ^ 59
def prefixEnd_847751 : Nat := 4983230072969 + 3 ^ 40 * 847751 * 2
def baseEnd_847751 : Nat := 290202492219878602675847

theorem tailTrace_847751 : CollatzResearch.WordTrace tailWord_847751 prefixEnd_847751 290202492219878602675847 := by
  unfold tailWord_847751
  simp only [CollatzResearch.WordTrace]
  refine ⟨30920019151750386189039107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20613346101166924126026071 30920019151750386189039107)
  ·
    refine ⟨46380028727625579283558661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30920019151750386189039107 46380028727625579283558661)
    ·
      refine ⟨8696255386429796115667249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46380028727625579283558661 8696255386429796115667249)
      ·
        refine ⟨6522191539822347086750437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8696255386429796115667249 6522191539822347086750437)
        ·
          refine ⟨1222910913716690078765707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6522191539822347086750437 1222910913716690078765707)
          ·
            refine ⟨1834366370575035118148561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222910913716690078765707 1834366370575035118148561)
            ·
              refine ⟨1375774777931276338611421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1834366370575035118148561 1375774777931276338611421)
              ·
                refine ⟨515915541724228626979283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1375774777931276338611421 515915541724228626979283)
                ·
                  refine ⟨773873312586342940468925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515915541724228626979283 773873312586342940468925)
                  ·
                    refine ⟨290202492219878602675847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 773873312586342940468925 290202492219878602675847)
                    ·
                      rfl

theorem cell22_847751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_847751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847751 prefixEnd_847751 := by exact prefixLift 847751
  have htrace : WordTrace (prefixWord ++ tailWord_847751) baseStart_847751 baseEnd_847751 := by
    simpa [prefixWord, tailWord_847751, baseEnd_847751] using wordTrace_append hprefix tailTrace_847751
  have hstable : (prefixWord ++ tailWord_847751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847751).length < 2 ^ (prefixWord ++ tailWord_847751).sum := by decide
  have hdescent : baseEnd_847751 < baseStart_847751 := by decide
  rcases family_descends (prefixWord ++ tailWord_847751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847762 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_847762 : Nat := 118140960795 + 847762 * 2 ^ 59
def prefixEnd_847762 : Nat := 4983230072969 + 3 ^ 40 * 847762 * 2
def baseEnd_847762 : Nat := 290206257744678240650813

theorem tailTrace_847762 : CollatzResearch.WordTrace tailWord_847762 prefixEnd_847762 290206257744678240650813 := by
  unfold tailWord_847762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7730105088677633766922385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20613613569807023378459693 7730105088677633766922385)
  ·
    refine ⟨5797578816508225325191789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7730105088677633766922385 5797578816508225325191789)
    ·
      refine ⟨2174092056190584496946921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5797578816508225325191789 2174092056190584496946921)
      ·
        refine ⟨1630569042142938372710191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2174092056190584496946921 1630569042142938372710191)
        ·
          refine ⟨2445853563214407559065287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1630569042142938372710191 2445853563214407559065287)
          ·
            refine ⟨3668780344821611338597931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2445853563214407559065287 3668780344821611338597931)
            ·
              refine ⟨5503170517232417007896897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3668780344821611338597931 5503170517232417007896897)
              ·
                refine ⟨4127377887924312755922673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5503170517232417007896897 4127377887924312755922673)
                ·
                  refine ⟨3095533415943234566942005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4127377887924312755922673 3095533415943234566942005)
                  ·
                    refine ⟨290206257744678240650813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3095533415943234566942005 290206257744678240650813)
                    ·
                      rfl

theorem cell22_847762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_847762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847762 prefixEnd_847762 := by exact prefixLift 847762
  have htrace : WordTrace (prefixWord ++ tailWord_847762) baseStart_847762 baseEnd_847762 := by
    simpa [prefixWord, tailWord_847762, baseEnd_847762] using wordTrace_append hprefix tailTrace_847762
  have hstable : (prefixWord ++ tailWord_847762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847762).length < 2 ^ (prefixWord ++ tailWord_847762).sum := by decide
  have hdescent : baseEnd_847762 < baseStart_847762 := by decide
  rcases family_descends (prefixWord ++ tailWord_847762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847764 : List Nat := [2, 4, 2, 1, 1, 4, 1, 2, 5]
def baseStart_847764 : Nat := 118140960795 + 847764 * 2 ^ 59
def prefixEnd_847764 : Nat := 4983230072969 + 3 ^ 40 * 847764 * 2
def baseEnd_847764 : Nat := 96735647461850300700269

theorem tailTrace_847764 : CollatzResearch.WordTrace tailWord_847764 prefixEnd_847764 96735647461850300700269 := by
  unfold tailWord_847764
  simp only [CollatzResearch.WordTrace]
  refine ⟨15460246650351644704631173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20613662200468859606174897 15460246650351644704631173)
  ·
    refine ⟨2898796246940933382118345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15460246650351644704631173 2898796246940933382118345)
    ·
      refine ⟨2174097185205700036588759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2898796246940933382118345 2174097185205700036588759)
      ·
        refine ⟨3261145777808550054883139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2174097185205700036588759 3261145777808550054883139)
        ·
          refine ⟨4891718666712825082324709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3261145777808550054883139 4891718666712825082324709)
          ·
            refine ⟨917197250008654702935883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4891718666712825082324709 917197250008654702935883)
            ·
              refine ⟨1375795875012982054403825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917197250008654702935883 1375795875012982054403825)
              ·
                refine ⟨1031846906259736540802869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1375795875012982054403825 1031846906259736540802869)
                ·
                  refine ⟨96735647461850300700269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1031846906259736540802869 96735647461850300700269)
                  ·
                    rfl

theorem cell22_847764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_847764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847764 prefixEnd_847764 := by exact prefixLift 847764
  have htrace : WordTrace (prefixWord ++ tailWord_847764) baseStart_847764 baseEnd_847764 := by
    simpa [prefixWord, tailWord_847764, baseEnd_847764] using wordTrace_append hprefix tailTrace_847764
  have hstable : (prefixWord ++ tailWord_847764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847764).length < 2 ^ (prefixWord ++ tailWord_847764).sum := by decide
  have hdescent : baseEnd_847764 < baseStart_847764 := by decide
  rcases family_descends (prefixWord ++ tailWord_847764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847820 : List Nat := [2, 2, 1, 4, 1, 2, 10]
def baseStart_847820 : Nat := 118140960795 + 847820 * 2 ^ 59
def prefixEnd_847820 : Nat := 4983230072969 + 3 ^ 40 * 847820 * 2
def baseEnd_847820 : Nat := 10749115271480941581505

theorem tailTrace_847820 : CollatzResearch.WordTrace tailWord_847820 prefixEnd_847820 10749115271480941581505 := by
  unfold tailWord_847820
  simp only [CollatzResearch.WordTrace]
  refine ⟨15461267894250205486650457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20615023859000273982200609 15461267894250205486650457)
  ·
    refine ⟨11595950920687654114987843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15461267894250205486650457 11595950920687654114987843)
    ·
      refine ⟨17393926381031481172481765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11595950920687654114987843 17393926381031481172481765)
      ·
        refine ⟨3261361196443402719840331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17393926381031481172481765 3261361196443402719840331)
        ·
          refine ⟨4892041794665104079760497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3261361196443402719840331 4892041794665104079760497)
          ·
            refine ⟨3669031345998828059820373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4892041794665104079760497 3669031345998828059820373)
            ·
              refine ⟨10749115271480941581505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3669031345998828059820373 10749115271480941581505)
              ·
                rfl

theorem cell22_847820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 10].length) (baseStart_847820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847820 prefixEnd_847820 := by exact prefixLift 847820
  have htrace : WordTrace (prefixWord ++ tailWord_847820) baseStart_847820 baseEnd_847820 := by
    simpa [prefixWord, tailWord_847820, baseEnd_847820] using wordTrace_append hprefix tailTrace_847820
  have hstable : (prefixWord ++ tailWord_847820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847820).length < 2 ^ (prefixWord ++ tailWord_847820).sum := by decide
  have hdescent : baseEnd_847820 < baseStart_847820 := by decide
  rcases family_descends (prefixWord ++ tailWord_847820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847822 : List Nat := [4, 1, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_847822 : Nat := 118140960795 + 847822 * 2 ^ 59
def prefixEnd_847822 : Nat := 4983230072969 + 3 ^ 40 * 847822 * 2
def baseEnd_847822 : Nat := 290226796970858084150629

theorem tailTrace_847822 : CollatzResearch.WordTrace tailWord_847822 prefixEnd_847822 290226796970858084150629 := by
  unfold tailWord_847822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3865326091811645664359215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20615072489662110209915813 3865326091811645664359215)
  ·
    refine ⟨5797989137717468496538823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3865326091811645664359215 5797989137717468496538823)
    ·
      refine ⟨8696983706576202744808235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5797989137717468496538823 8696983706576202744808235)
      ·
        refine ⟨13045475559864304117212353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8696983706576202744808235 13045475559864304117212353)
        ·
          refine ⟨9784106669898228087909265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13045475559864304117212353 9784106669898228087909265)
          ·
            refine ⟨7338080002423671065931949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9784106669898228087909265 7338080002423671065931949)
            ·
              refine ⟨2751780000908876649724481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7338080002423671065931949 2751780000908876649724481)
              ·
                refine ⟨2063835000681657487293361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2751780000908876649724481 2063835000681657487293361)
                ·
                  refine ⟨1547876250511243115470021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2063835000681657487293361 1547876250511243115470021)
                  ·
                    refine ⟨290226796970858084150629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1547876250511243115470021 290226796970858084150629)
                    ·
                      rfl

theorem cell22_847822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_847822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847822 prefixEnd_847822 := by exact prefixLift 847822
  have htrace : WordTrace (prefixWord ++ tailWord_847822) baseStart_847822 baseEnd_847822 := by
    simpa [prefixWord, tailWord_847822, baseEnd_847822] using wordTrace_append hprefix tailTrace_847822
  have hstable : (prefixWord ++ tailWord_847822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847822).length < 2 ^ (prefixWord ++ tailWord_847822).sum := by decide
  have hdescent : baseEnd_847822 < baseStart_847822 := by decide
  rcases family_descends (prefixWord ++ tailWord_847822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847826 : List Nat := [3, 2, 2, 3, 3, 1, 1, 1, 6]
def baseStart_847826 : Nat := 118140960795 + 847826 * 2 ^ 59
def prefixEnd_847826 : Nat := 4983230072969 + 3 ^ 40 * 847826 * 2
def baseEnd_847826 : Nat := 96742722084201135683539

theorem tailTrace_847826 : CollatzResearch.WordTrace tailWord_847826 prefixEnd_847826 96742722084201135683539 := by
  unfold tailWord_847826
  simp only [CollatzResearch.WordTrace]
  refine ⟨7730688656619668499504833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20615169750985782665346221 7730688656619668499504833)
  ·
    refine ⟨5798016492464751374628625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7730688656619668499504833 5798016492464751374628625)
    ·
      refine ⟨4348512369348563530971469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5798016492464751374628625 4348512369348563530971469)
      ·
        refine ⟨1630692138505711324114301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4348512369348563530971469 1630692138505711324114301)
        ·
          refine ⟨611509551939641746542863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1630692138505711324114301 611509551939641746542863)
          ·
            refine ⟨917264327909462619814295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611509551939641746542863 917264327909462619814295)
            ·
              refine ⟨1375896491864193929721443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917264327909462619814295 1375896491864193929721443)
              ·
                refine ⟨2063844737796290894582165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1375896491864193929721443 2063844737796290894582165)
                ·
                  refine ⟨96742722084201135683539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2063844737796290894582165 96742722084201135683539)
                  ·
                    rfl

theorem cell22_847826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_847826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847826 prefixEnd_847826 := by exact prefixLift 847826
  have htrace : WordTrace (prefixWord ++ tailWord_847826) baseStart_847826 baseEnd_847826 := by
    simpa [prefixWord, tailWord_847826, baseEnd_847826] using wordTrace_append hprefix tailTrace_847826
  have hstable : (prefixWord ++ tailWord_847826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847826).length < 2 ^ (prefixWord ++ tailWord_847826).sum := by decide
  have hdescent : baseEnd_847826 < baseStart_847826 := by decide
  rcases family_descends (prefixWord ++ tailWord_847826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847852 : List Nat := [2, 2, 1, 1, 2, 1, 1, 6, 3, 3]
def baseStart_847852 : Nat := 118140960795 + 847852 * 2 ^ 59
def prefixEnd_847852 : Nat := 4983230072969 + 3 ^ 40 * 847852 * 2
def baseEnd_847852 : Nat := 290237066583948005900537

theorem tailTrace_847852 : CollatzResearch.WordTrace tailWord_847852 prefixEnd_847852 290237066583948005900537 := by
  unfold tailWord_847852
  simp only [CollatzResearch.WordTrace]
  refine ⟨15461851462192240219232905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20615801949589653625643873 15461851462192240219232905)
  ·
    refine ⟨11596388596644180164424679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15461851462192240219232905 11596388596644180164424679)
    ·
      refine ⟨17394582894966270246637019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11596388596644180164424679 17394582894966270246637019)
      ·
        refine ⟨26091874342449405369955529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17394582894966270246637019 26091874342449405369955529)
        ·
          refine ⟨19568905756837054027466647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26091874342449405369955529 19568905756837054027466647)
          ·
            refine ⟨29353358635255581041199971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19568905756837054027466647 29353358635255581041199971)
            ·
              refine ⟨44030037952883371561799957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29353358635255581041199971 44030037952883371561799957)
              ·
                refine ⟨2063908029041408041959373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44030037952883371561799957 2063908029041408041959373)
                ·
                  refine ⟨773965510890528015734765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2063908029041408041959373 773965510890528015734765)
                  ·
                    refine ⟨290237066583948005900537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 773965510890528015734765 290237066583948005900537)
                    ·
                      rfl

theorem cell22_847852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_847852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847852 prefixEnd_847852 := by exact prefixLift 847852
  have htrace : WordTrace (prefixWord ++ tailWord_847852) baseStart_847852 baseEnd_847852 := by
    simpa [prefixWord, tailWord_847852, baseEnd_847852] using wordTrace_append hprefix tailTrace_847852
  have hstable : (prefixWord ++ tailWord_847852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847852).length < 2 ^ (prefixWord ++ tailWord_847852).sum := by decide
  have hdescent : baseEnd_847852 < baseStart_847852 := by decide
  rcases family_descends (prefixWord ++ tailWord_847852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847886 : List Nat := [4, 1, 1, 2, 2, 1, 3, 4, 1, 3]
def baseStart_847886 : Nat := 118140960795 + 847886 * 2 ^ 59
def prefixEnd_847886 : Nat := 4983230072969 + 3 ^ 40 * 847886 * 2
def baseEnd_847886 : Nat := 290248705478783250550433

theorem tailTrace_847886 : CollatzResearch.WordTrace tailWord_847886 prefixEnd_847886 290248705478783250550433 := by
  unfold tailWord_847886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3865617875782663030650439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20616628670840869496802341 3865617875782663030650439)
  ·
    refine ⟨5798426813673994545975659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3865617875782663030650439 5798426813673994545975659)
    ·
      refine ⟨8697640220510991818963489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5798426813673994545975659 8697640220510991818963489)
      ·
        refine ⟨6523230165383243864222617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8697640220510991818963489 6523230165383243864222617)
        ·
          refine ⟨4892422624037432898166963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6523230165383243864222617 4892422624037432898166963)
          ·
            refine ⟨7338633936056149347250445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4892422624037432898166963 7338633936056149347250445)
            ·
              refine ⟨2751987726021056005218917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7338633936056149347250445 2751987726021056005218917)
              ·
                refine ⟨515997698628948000978547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2751987726021056005218917 515997698628948000978547)
                ·
                  refine ⟨773996547943422001467821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515997698628948000978547 773996547943422001467821)
                  ·
                    refine ⟨290248705478783250550433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 773996547943422001467821 290248705478783250550433)
                    ·
                      rfl

theorem cell22_847886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_847886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847886 prefixEnd_847886 := by exact prefixLift 847886
  have htrace : WordTrace (prefixWord ++ tailWord_847886) baseStart_847886 baseEnd_847886 := by
    simpa [prefixWord, tailWord_847886, baseEnd_847886] using wordTrace_append hprefix tailTrace_847886
  have hstable : (prefixWord ++ tailWord_847886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847886).length < 2 ^ (prefixWord ++ tailWord_847886).sum := by decide
  have hdescent : baseEnd_847886 < baseStart_847886 := by decide
  rcases family_descends (prefixWord ++ tailWord_847886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847957 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 1, 6]
def baseStart_847957 : Nat := 118140960795 + 847957 * 2 ^ 59
def prefixEnd_847957 : Nat := 4983230072969 + 3 ^ 40 * 847957 * 2
def baseEnd_847957 : Nat := 290273010229762732025215

theorem tailTrace_847957 : CollatzResearch.WordTrace tailWord_847957 prefixEnd_847957 290273010229762732025215 := by
  unfold tailWord_847957
  simp only [CollatzResearch.WordTrace]
  refine ⟨30927532589004083371038125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20618355059336055580692083 30927532589004083371038125)
  ·
    refine ⟨11597824720876531264139297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30927532589004083371038125 11597824720876531264139297)
    ·
      refine ⟨8698368540657398448104473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11597824720876531264139297 8698368540657398448104473)
      ·
        refine ⟨6523776405493048836078355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8698368540657398448104473 6523776405493048836078355)
        ·
          refine ⟨9785664608239573254117533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6523776405493048836078355 9785664608239573254117533)
          ·
            refine ⟨3669624228089839970294075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9785664608239573254117533 3669624228089839970294075)
            ·
              refine ⟨5504436342134759955441113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3669624228089839970294075 5504436342134759955441113)
              ·
                refine ⟨4128327256601069966580835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5504436342134759955441113 4128327256601069966580835)
                ·
                  refine ⟨6192490884901604949871253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4128327256601069966580835 6192490884901604949871253)
                  ·
                    refine ⟨290273010229762732025215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6192490884901604949871253 290273010229762732025215)
                    ·
                      rfl

theorem cell22_847957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_847957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847957 prefixEnd_847957 := by exact prefixLift 847957
  have htrace : WordTrace (prefixWord ++ tailWord_847957) baseStart_847957 baseEnd_847957 := by
    simpa [prefixWord, tailWord_847957, baseEnd_847957] using wordTrace_append hprefix tailTrace_847957
  have hstable : (prefixWord ++ tailWord_847957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847957).length < 2 ^ (prefixWord ++ tailWord_847957).sum := by decide
  have hdescent : baseEnd_847957 < baseStart_847957 := by decide
  rcases family_descends (prefixWord ++ tailWord_847957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847959 : List Nat := [1, 1, 3, 2, 2, 1, 2, 5, 2, 3]
def baseStart_847959 : Nat := 118140960795 + 847959 * 2 ^ 59
def prefixEnd_847959 : Nat := 4983230072969 + 3 ^ 40 * 847959 * 2
def baseEnd_847959 : Nat := 290273694870635393475209

theorem tailTrace_847959 : CollatzResearch.WordTrace tailWord_847959 prefixEnd_847959 290273694870635393475209 := by
  unfold tailWord_847959
  simp only [CollatzResearch.WordTrace]
  refine ⟨30927605534996837712610931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20618403689997891808407287 30927605534996837712610931)
  ·
    refine ⟨46391408302495256568916397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30927605534996837712610931 46391408302495256568916397)
    ·
      refine ⟨17396778113435721213343649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46391408302495256568916397 17396778113435721213343649)
      ·
        refine ⟨13047583585076790910007737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17396778113435721213343649 13047583585076790910007737)
        ·
          refine ⟨9785687688807593182505803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13047583585076790910007737 9785687688807593182505803)
          ·
            refine ⟨14678531533211389773758705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9785687688807593182505803 14678531533211389773758705)
            ·
              refine ⟨11008898649908542330319029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14678531533211389773758705 11008898649908542330319029)
              ·
                refine ⟨1032084248428925843467409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11008898649908542330319029 1032084248428925843467409)
                ·
                  refine ⟨774063186321694382600557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1032084248428925843467409 774063186321694382600557)
                  ·
                    refine ⟨290273694870635393475209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 774063186321694382600557 290273694870635393475209)
                    ·
                      rfl

theorem cell22_847959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_847959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847959 prefixEnd_847959 := by exact prefixLift 847959
  have htrace : WordTrace (prefixWord ++ tailWord_847959) baseStart_847959 baseEnd_847959 := by
    simpa [prefixWord, tailWord_847959, baseEnd_847959] using wordTrace_append hprefix tailTrace_847959
  have hstable : (prefixWord ++ tailWord_847959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847959).length < 2 ^ (prefixWord ++ tailWord_847959).sum := by decide
  have hdescent : baseEnd_847959 < baseStart_847959 := by decide
  rcases family_descends (prefixWord ++ tailWord_847959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847978 : List Nat := [3, 1, 3, 2, 3, 2, 1, 3, 4]
def baseStart_847978 : Nat := 118140960795 + 847978 * 2 ^ 59
def prefixEnd_847978 : Nat := 4983230072969 + 3 ^ 40 * 847978 * 2
def baseEnd_847978 : Nat := 96760066319641892416717

theorem tailTrace_847978 : CollatzResearch.WordTrace tailWord_847978 prefixEnd_847978 96760066319641892416717 := by
  unfold tailWord_847978
  simp only [CollatzResearch.WordTrace]
  refine ⟨7732074630482000989388147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20618865681285335971701725 7732074630482000989388147)
  ·
    refine ⟨11598111945723001484082221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7732074630482000989388147 11598111945723001484082221)
    ·
      refine ⟨4349291979646125556530833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11598111945723001484082221 4349291979646125556530833)
      ·
        refine ⟨3261968984734594167398125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4349291979646125556530833 3261968984734594167398125)
        ·
          refine ⟨1223238369275472812774297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3261968984734594167398125 1223238369275472812774297)
          ·
            refine ⟨917428776956604609580723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1223238369275472812774297 917428776956604609580723)
            ·
              refine ⟨1376143165434906914371085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917428776956604609580723 1376143165434906914371085)
              ·
                refine ⟨516053687038090092889157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1376143165434906914371085 516053687038090092889157)
                ·
                  refine ⟨96760066319641892416717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 516053687038090092889157 96760066319641892416717)
                  ·
                    rfl

theorem cell22_847978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_847978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_847978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_847978 prefixEnd_847978 := by exact prefixLift 847978
  have htrace : WordTrace (prefixWord ++ tailWord_847978) baseStart_847978 baseEnd_847978 := by
    simpa [prefixWord, tailWord_847978, baseEnd_847978] using wordTrace_append hprefix tailTrace_847978
  have hstable : (prefixWord ++ tailWord_847978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847978).length < 2 ^ (prefixWord ++ tailWord_847978).sum := by decide
  have hdescent : baseEnd_847978 < baseStart_847978 := by decide
  rcases family_descends (prefixWord ++ tailWord_847978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848055 : List Nat := [1, 1, 3, 1, 4, 4, 2, 2, 1, 3]
def baseStart_848055 : Nat := 118140960795 + 848055 * 2 ^ 59
def prefixEnd_848055 : Nat := 4983230072969 + 3 ^ 40 * 848055 * 2
def baseEnd_848055 : Nat := 290306557632523143074915

theorem tailTrace_848055 : CollatzResearch.WordTrace tailWord_848055 prefixEnd_848055 290306557632523143074915 := by
  unfold tailWord_848055
  simp only [CollatzResearch.WordTrace]
  refine ⟨30931106942649046108105619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20620737961766030738737079 30931106942649046108105619)
  ·
    refine ⟨46396660413973569162158429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30931106942649046108105619 46396660413973569162158429)
    ·
      refine ⟨17398747655240088435809411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46396660413973569162158429 17398747655240088435809411)
      ·
        refine ⟨26098121482860132653714117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17398747655240088435809411 26098121482860132653714117)
        ·
          refine ⟨4893397778036274872571397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26098121482860132653714117 4893397778036274872571397)
          ·
            refine ⟨917512083381801538607137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4893397778036274872571397 917512083381801538607137)
            ·
              refine ⟨688134062536351153955353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 917512083381801538607137 688134062536351153955353)
              ·
                refine ⟨516100546902263365466515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688134062536351153955353 516100546902263365466515)
                ·
                  refine ⟨774150820353395048199773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516100546902263365466515 774150820353395048199773)
                  ·
                    refine ⟨290306557632523143074915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 774150820353395048199773 290306557632523143074915)
                    ·
                      rfl

theorem cell22_848055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 1, 3].length) (baseStart_848055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848055 prefixEnd_848055 := by exact prefixLift 848055
  have htrace : WordTrace (prefixWord ++ tailWord_848055) baseStart_848055 baseEnd_848055 := by
    simpa [prefixWord, tailWord_848055, baseEnd_848055] using wordTrace_append hprefix tailTrace_848055
  have hstable : (prefixWord ++ tailWord_848055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848055).length < 2 ^ (prefixWord ++ tailWord_848055).sum := by decide
  have hdescent : baseEnd_848055 < baseStart_848055 := by decide
  rcases family_descends (prefixWord ++ tailWord_848055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848064 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 3, 4]
def baseStart_848064 : Nat := 118140960795 + 848064 * 2 ^ 59
def prefixEnd_848064 : Nat := 4983230072969 + 3 ^ 40 * 848064 * 2
def baseEnd_848064 : Nat := 290309638516450119599887

theorem tailTrace_848064 : CollatzResearch.WordTrace tailWord_848064 prefixEnd_848064 290309638516450119599887 := by
  unfold tailWord_848064
  simp only [CollatzResearch.WordTrace]
  refine ⟨15465717599808220322591623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20620956799744293763455497 15465717599808220322591623)
  ·
    refine ⟨23198576399712330483887435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15465717599808220322591623 23198576399712330483887435)
    ·
      refine ⟨34797864599568495725831153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23198576399712330483887435 34797864599568495725831153)
      ·
        refine ⟨26098398449676371794373365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34797864599568495725831153 26098398449676371794373365)
        ·
          refine ⟨2446724854657159855722503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26098398449676371794373365 2446724854657159855722503)
          ·
            refine ⟨3670087281985739783583755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2446724854657159855722503 3670087281985739783583755)
            ·
              refine ⟨5505130922978609675375633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3670087281985739783583755 5505130922978609675375633)
              ·
                refine ⟨4128848192233957256531725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5505130922978609675375633 4128848192233957256531725)
                ·
                  refine ⟨1548318072087733971199397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4128848192233957256531725 1548318072087733971199397)
                  ·
                    refine ⟨290309638516450119599887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1548318072087733971199397 290309638516450119599887)
                    ·
                      rfl

theorem cell22_848064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_848064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848064 prefixEnd_848064 := by exact prefixLift 848064
  have htrace : WordTrace (prefixWord ++ tailWord_848064) baseStart_848064 baseEnd_848064 := by
    simpa [prefixWord, tailWord_848064, baseEnd_848064] using wordTrace_append hprefix tailTrace_848064
  have hstable : (prefixWord ++ tailWord_848064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848064).length < 2 ^ (prefixWord ++ tailWord_848064).sum := by decide
  have hdescent : baseEnd_848064 < baseStart_848064 := by decide
  rcases family_descends (prefixWord ++ tailWord_848064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848096 : List Nat := [2, 1, 1, 3, 1, 3, 4, 3, 4]
def baseStart_848096 : Nat := 118140960795 + 848096 * 2 ^ 59
def prefixEnd_848096 : Nat := 4983230072969 + 3 ^ 40 * 848096 * 2
def baseEnd_848096 : Nat := 96773530923470900933263

theorem tailTrace_848096 : CollatzResearch.WordTrace tailWord_848096 prefixEnd_848096 96773530923470900933263 := by
  unfold tailWord_848096
  simp only [CollatzResearch.WordTrace]
  refine ⟨15466301167750255055174071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20621734890333673406898761 15466301167750255055174071)
  ·
    refine ⟨23199451751625382582761107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15466301167750255055174071 23199451751625382582761107)
    ·
      refine ⟨34799177627438073874141661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23199451751625382582761107 34799177627438073874141661)
      ·
        refine ⟨13049691610289277702803123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34799177627438073874141661 13049691610289277702803123)
        ·
          refine ⟨19574537415433916554204685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13049691610289277702803123 19574537415433916554204685)
          ·
            refine ⟨7340451530787718707826757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19574537415433916554204685 7340451530787718707826757)
            ·
              refine ⟨1376334662022697257717517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7340451530787718707826757 1376334662022697257717517)
              ·
                refine ⟨516125498258511471644069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1376334662022697257717517 516125498258511471644069)
                ·
                  refine ⟨96773530923470900933263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 516125498258511471644069 96773530923470900933263)
                  ·
                    rfl

theorem cell22_848096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 4].length) (baseStart_848096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848096 prefixEnd_848096 := by exact prefixLift 848096
  have htrace : WordTrace (prefixWord ++ tailWord_848096) baseStart_848096 baseEnd_848096 := by
    simpa [prefixWord, tailWord_848096, baseEnd_848096] using wordTrace_append hprefix tailTrace_848096
  have hstable : (prefixWord ++ tailWord_848096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848096).length < 2 ^ (prefixWord ++ tailWord_848096).sum := by decide
  have hdescent : baseEnd_848096 < baseStart_848096 := by decide
  rcases family_descends (prefixWord ++ tailWord_848096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848107 : List Nat := [1, 1, 1, 1, 2, 5, 11]
def baseStart_848107 : Nat := 118140960795 + 848107 * 2 ^ 59
def prefixEnd_848107 : Nat := 4983230072969 + 3 ^ 40 * 848107 * 2
def baseEnd_848107 : Nat := 10752754010933790399065

theorem tailTrace_848107 : CollatzResearch.WordTrace tailWord_848107 prefixEnd_848107 10752754010933790399065 := by
  unfold tailWord_848107
  simp only [CollatzResearch.WordTrace]
  refine ⟨30933003538460658988998575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20622002358973772659332383 30933003538460658988998575)
  ·
    refine ⟨46399505307690988483497863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30933003538460658988998575 46399505307690988483497863)
    ·
      refine ⟨69599257961536482725246795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46399505307690988483497863 69599257961536482725246795)
      ·
        refine ⟨104398886942304724087870193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69599257961536482725246795 104398886942304724087870193)
        ·
          refine ⟨78299165206728543065902645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104398886942304724087870193 78299165206728543065902645)
          ·
            refine ⟨7340546738130800912428373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78299165206728543065902645 7340546738130800912428373)
            ·
              refine ⟨10752754010933790399065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7340546738130800912428373 10752754010933790399065)
              ·
                rfl

theorem cell22_848107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 11].length) (baseStart_848107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848107 prefixEnd_848107 := by exact prefixLift 848107
  have htrace : WordTrace (prefixWord ++ tailWord_848107) baseStart_848107 baseEnd_848107 := by
    simpa [prefixWord, tailWord_848107, baseEnd_848107] using wordTrace_append hprefix tailTrace_848107
  have hstable : (prefixWord ++ tailWord_848107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848107).length < 2 ^ (prefixWord ++ tailWord_848107).sum := by decide
  have hdescent : baseEnd_848107 < baseStart_848107 := by decide
  rcases family_descends (prefixWord ++ tailWord_848107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848111 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 4, 3]
def baseStart_848111 : Nat := 118140960795 + 848111 * 2 ^ 59
def prefixEnd_848111 : Nat := 4983230072969 + 3 ^ 40 * 848111 * 2
def baseEnd_848111 : Nat := 290325727576957663674743

theorem tailTrace_848111 : CollatzResearch.WordTrace tailWord_848111 prefixEnd_848111 290325727576957663674743 := by
  unfold tailWord_848111
  simp only [CollatzResearch.WordTrace]
  refine ⟨30933149430446167672144187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20622099620297445114762791 30933149430446167672144187)
  ·
    refine ⟨46399724145669251508216281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30933149430446167672144187 46399724145669251508216281)
    ·
      refine ⟨34799793109251938631162211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46399724145669251508216281 34799793109251938631162211)
      ·
        refine ⟨52199689663877907946743317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34799793109251938631162211 52199689663877907946743317)
        ·
          refine ⟨2446860452994276935003593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52199689663877907946743317 2446860452994276935003593)
          ·
            refine ⟨1835145339745707701252695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2446860452994276935003593 1835145339745707701252695)
            ·
              refine ⟨2752718009618561551879043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835145339745707701252695 2752718009618561551879043)
              ·
                refine ⟨4129077014427842327818565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2752718009618561551879043 4129077014427842327818565)
                ·
                  refine ⟨774201940205220436465981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4129077014427842327818565 774201940205220436465981)
                  ·
                    refine ⟨290325727576957663674743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 774201940205220436465981 290325727576957663674743)
                    ·
                      rfl

theorem cell22_848111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 3].length) (baseStart_848111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848111 prefixEnd_848111 := by exact prefixLift 848111
  have htrace : WordTrace (prefixWord ++ tailWord_848111) baseStart_848111 baseEnd_848111 := by
    simpa [prefixWord, tailWord_848111, baseEnd_848111] using wordTrace_append hprefix tailTrace_848111
  have hstable : (prefixWord ++ tailWord_848111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848111).length < 2 ^ (prefixWord ++ tailWord_848111).sum := by decide
  have hdescent : baseEnd_848111 < baseStart_848111 := by decide
  rcases family_descends (prefixWord ++ tailWord_848111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848158 : List Nat := [4, 3, 2, 1, 1, 3, 8]
def baseStart_848158 : Nat := 118140960795 + 848158 * 2 ^ 59
def prefixEnd_848158 : Nat := 4983230072969 + 3 ^ 40 * 848158 * 2
def baseEnd_848158 : Nat := 10753400616202415101837

theorem tailTrace_848158 : CollatzResearch.WordTrace tailWord_848158 prefixEnd_848158 10753400616202415101837 := by
  unfold tailWord_848158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3866857957659486837388141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20623242440850596466070085 3866857957659486837388141)
  ·
    refine ⟨1450071734122307564020553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3866857957659486837388141 1450071734122307564020553)
    ·
      refine ⟨1087553800591730673015415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1450071734122307564020553 1087553800591730673015415)
      ·
        refine ⟨1631330700887596009523123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1087553800591730673015415 1631330700887596009523123)
        ·
          refine ⟨2446996051331394014284685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1631330700887596009523123 2446996051331394014284685)
          ·
            refine ⟨917623519249272755356757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2446996051331394014284685 917623519249272755356757)
            ·
              refine ⟨10753400616202415101837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 917623519249272755356757 10753400616202415101837)
              ·
                rfl

theorem cell22_848158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 8].length) (baseStart_848158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848158 prefixEnd_848158 := by exact prefixLift 848158
  have htrace : WordTrace (prefixWord ++ tailWord_848158) baseStart_848158 baseEnd_848158 := by
    simpa [prefixWord, tailWord_848158, baseEnd_848158] using wordTrace_append hprefix tailTrace_848158
  have hstable : (prefixWord ++ tailWord_848158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848158).length < 2 ^ (prefixWord ++ tailWord_848158).sum := by decide
  have hdescent : baseEnd_848158 < baseStart_848158 := by decide
  rcases family_descends (prefixWord ++ tailWord_848158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848184 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 2, 5]
def baseStart_848184 : Nat := 118140960795 + 848184 * 2 ^ 59
def prefixEnd_848184 : Nat := 4983230072969 + 3 ^ 40 * 848184 * 2
def baseEnd_848184 : Nat := 290350716968809806599519

theorem tailTrace_848184 : CollatzResearch.WordTrace tailWord_848184 prefixEnd_848184 290350716968809806599519 := by
  unfold tailWord_848184
  simp only [CollatzResearch.WordTrace]
  refine ⟨15467905979590850569775803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20623874639454467426367737 15467905979590850569775803)
  ·
    refine ⟨23201858969386275854663705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15467905979590850569775803 23201858969386275854663705)
    ·
      refine ⟨17401394227039706890997779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23201858969386275854663705 17401394227039706890997779)
      ·
        refine ⟨26102091340559560336496669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17401394227039706890997779 26102091340559560336496669)
        ·
          refine ⟨9788284252709835126186251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26102091340559560336496669 9788284252709835126186251)
          ·
            refine ⟨14682426379064752689279377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9788284252709835126186251 14682426379064752689279377)
            ·
              refine ⟨11011819784298564516959533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14682426379064752689279377 11011819784298564516959533)
              ·
                refine ⟨4129432419111961693859825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11011819784298564516959533 4129432419111961693859825)
                ·
                  refine ⟨3097074314333971270394869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4129432419111961693859825 3097074314333971270394869)
                  ·
                    refine ⟨290350716968809806599519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3097074314333971270394869 290350716968809806599519)
                    ·
                      rfl

theorem cell22_848184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_848184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848184 prefixEnd_848184 := by exact prefixLift 848184
  have htrace : WordTrace (prefixWord ++ tailWord_848184) baseStart_848184 baseEnd_848184 := by
    simpa [prefixWord, tailWord_848184, baseEnd_848184] using wordTrace_append hprefix tailTrace_848184
  have hstable : (prefixWord ++ tailWord_848184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848184).length < 2 ^ (prefixWord ++ tailWord_848184).sum := by decide
  have hdescent : baseEnd_848184 < baseStart_848184 := by decide
  rcases family_descends (prefixWord ++ tailWord_848184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848186 : List Nat := [3, 1, 1, 1, 4, 3, 1, 3, 5]
def baseStart_848186 : Nat := 118140960795 + 848186 * 2 ^ 59
def prefixEnd_848186 : Nat := 4983230072969 + 3 ^ 40 * 848186 * 2
def baseEnd_848186 : Nat := 96783800536560822683171

theorem tailTrace_848186 : CollatzResearch.WordTrace tailWord_848186 prefixEnd_848186 96783800536560822683171 := by
  unfold tailWord_848186
  simp only [CollatzResearch.WordTrace]
  refine ⟨7733971226293613870281103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20623923270116303654082941 7733971226293613870281103)
  ·
    refine ⟨11600956839440420805421655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7733971226293613870281103 11600956839440420805421655)
    ·
      refine ⟨17401435259160631208132483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11600956839440420805421655 17401435259160631208132483)
      ·
        refine ⟨26102152888740946812198725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17401435259160631208132483 26102152888740946812198725)
        ·
          refine ⟨4894153666638927527287261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26102152888740946812198725 4894153666638927527287261)
          ·
            refine ⟨1835307624989597822732723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4894153666638927527287261 1835307624989597822732723)
            ·
              refine ⟨2752961437484396734099085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835307624989597822732723 2752961437484396734099085)
              ·
                refine ⟨1032360539056648775287157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2752961437484396734099085 1032360539056648775287157)
                ·
                  refine ⟨96783800536560822683171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1032360539056648775287157 96783800536560822683171)
                  ·
                    rfl

theorem cell22_848186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_848186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848186 prefixEnd_848186 := by exact prefixLift 848186
  have htrace : WordTrace (prefixWord ++ tailWord_848186) baseStart_848186 baseEnd_848186 := by
    simpa [prefixWord, tailWord_848186, baseEnd_848186] using wordTrace_append hprefix tailTrace_848186
  have hstable : (prefixWord ++ tailWord_848186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848186).length < 2 ^ (prefixWord ++ tailWord_848186).sum := by decide
  have hdescent : baseEnd_848186 < baseStart_848186 := by decide
  rcases family_descends (prefixWord ++ tailWord_848186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848220 : List Nat := [2, 2, 4, 3, 1, 1, 2, 2, 5]
def baseStart_848220 : Nat := 118140960795 + 848220 * 2 ^ 59
def prefixEnd_848220 : Nat := 4983230072969 + 3 ^ 40 * 848220 * 2
def baseEnd_848220 : Nat := 96787680168172570899803

theorem tailTrace_848220 : CollatzResearch.WordTrace tailWord_848220 prefixEnd_848220 96787680168172570899803 := by
  unfold tailWord_848220
  simp only [CollatzResearch.WordTrace]
  refine ⟨15468562493525639643931057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20624749991367519525241409 15468562493525639643931057)
  ·
    refine ⟨11601421870144229732948293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15468562493525639643931057 11601421870144229732948293)
    ·
      refine ⟨2175266600652043074927805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11601421870144229732948293 2175266600652043074927805)
      ·
        refine ⟨815724975244516153097927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2175266600652043074927805 815724975244516153097927)
        ·
          refine ⟨1223587462866774229646891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815724975244516153097927 1223587462866774229646891)
          ·
            refine ⟨1835381194300161344470337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1223587462866774229646891 1835381194300161344470337)
            ·
              refine ⟨1376535895725121008352753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1835381194300161344470337 1376535895725121008352753)
              ·
                refine ⟨1032401921793840756264565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1376535895725121008352753 1032401921793840756264565)
                ·
                  refine ⟨96787680168172570899803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1032401921793840756264565 96787680168172570899803)
                  ·
                    rfl

theorem cell22_848220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_848220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848220 prefixEnd_848220 := by exact prefixLift 848220
  have htrace : WordTrace (prefixWord ++ tailWord_848220) baseStart_848220 baseEnd_848220 := by
    simpa [prefixWord, tailWord_848220, baseEnd_848220] using wordTrace_append hprefix tailTrace_848220
  have hstable : (prefixWord ++ tailWord_848220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848220).length < 2 ^ (prefixWord ++ tailWord_848220).sum := by decide
  have hdescent : baseEnd_848220 < baseStart_848220 := by decide
  rcases family_descends (prefixWord ++ tailWord_848220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848224 : List Nat := [2, 1, 1, 3, 6, 1, 2, 2, 1, 3]
def baseStart_848224 : Nat := 118140960795 + 848224 * 2 ^ 59
def prefixEnd_848224 : Nat := 4983230072969 + 3 ^ 40 * 848224 * 2
def baseEnd_848224 : Nat := 290364409786263035599397

theorem tailTrace_848224 : CollatzResearch.WordTrace tailWord_848224 prefixEnd_848224 290364409786263035599397 := by
  unfold tailWord_848224
  simp only [CollatzResearch.WordTrace]
  refine ⟨15468635439518393985503863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20624847252691191980671817 15468635439518393985503863)
  ·
    refine ⟨23202953159277590978255795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15468635439518393985503863 23202953159277590978255795)
    ·
      refine ⟨34804429738916386467383693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23202953159277590978255795 34804429738916386467383693)
      ·
        refine ⟨13051661152093644925268885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34804429738916386467383693 13051661152093644925268885)
        ·
          refine ⟨611796616504389605871979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13051661152093644925268885 611796616504389605871979)
          ·
            refine ⟨917694924756584408807969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611796616504389605871979 917694924756584408807969)
            ·
              refine ⟨688271193567438306605977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 917694924756584408807969 688271193567438306605977)
              ·
                refine ⟨516203395175578729954483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688271193567438306605977 516203395175578729954483)
                ·
                  refine ⟨774305092763368094931725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516203395175578729954483 774305092763368094931725)
                  ·
                    refine ⟨290364409786263035599397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 774305092763368094931725 290364409786263035599397)
                    ·
                      rfl

theorem cell22_848224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 1, 3].length) (baseStart_848224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848224 prefixEnd_848224 := by exact prefixLift 848224
  have htrace : WordTrace (prefixWord ++ tailWord_848224) baseStart_848224 baseEnd_848224 := by
    simpa [prefixWord, tailWord_848224, baseEnd_848224] using wordTrace_append hprefix tailTrace_848224
  have hstable : (prefixWord ++ tailWord_848224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848224).length < 2 ^ (prefixWord ++ tailWord_848224).sum := by decide
  have hdescent : baseEnd_848224 < baseStart_848224 := by decide
  rcases family_descends (prefixWord ++ tailWord_848224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848280 : List Nat := [2, 1, 2, 5, 1, 1, 3, 2, 2, 3]
def baseStart_848280 : Nat := 118140960795 + 848280 * 2 ^ 59
def prefixEnd_848280 : Nat := 4983230072969 + 3 ^ 40 * 848280 * 2
def baseEnd_848280 : Nat := 290383579730697556199225

theorem tailTrace_848280 : CollatzResearch.WordTrace tailWord_848280 prefixEnd_848280 290383579730697556199225 := by
  unfold tailWord_848280
  simp only [CollatzResearch.WordTrace]
  refine ⟨15469656683416954767523147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20626208911222606356697529 15469656683416954767523147)
  ·
    refine ⟨23204485025125432151284721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15469656683416954767523147 23204485025125432151284721)
    ·
      refine ⟨17403363768844074113463541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23204485025125432151284721 17403363768844074113463541)
      ·
        refine ⟨1631565353329131948137207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17403363768844074113463541 1631565353329131948137207)
        ·
          refine ⟨2447348029993697922205811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1631565353329131948137207 2447348029993697922205811)
          ·
            refine ⟨3671022044990546883308717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2447348029993697922205811 3671022044990546883308717)
            ·
              refine ⟨1376633266871455081240769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3671022044990546883308717 1376633266871455081240769)
              ·
                refine ⟨1032474950153591310930577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1376633266871455081240769 1032474950153591310930577)
                ·
                  refine ⟨774356212615193483197933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1032474950153591310930577 774356212615193483197933)
                  ·
                    refine ⟨290383579730697556199225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 774356212615193483197933 290383579730697556199225)
                    ·
                      rfl

theorem cell22_848280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_848280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848280 prefixEnd_848280 := by exact prefixLift 848280
  have htrace : WordTrace (prefixWord ++ tailWord_848280) baseStart_848280 baseEnd_848280 := by
    simpa [prefixWord, tailWord_848280, baseEnd_848280] using wordTrace_append hprefix tailTrace_848280
  have hstable : (prefixWord ++ tailWord_848280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848280).length < 2 ^ (prefixWord ++ tailWord_848280).sum := by decide
  have hdescent : baseEnd_848280 < baseStart_848280 := by decide
  rcases family_descends (prefixWord ++ tailWord_848280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848383 : List Nat := [1, 1, 2, 2, 1, 2, 4, 5, 4]
def baseStart_848383 : Nat := 118140960795 + 848383 * 2 ^ 59
def prefixEnd_848383 : Nat := 4983230072969 + 3 ^ 40 * 848383 * 2
def baseEnd_848383 : Nat := 96806279578546540291303

theorem tailTrace_848383 : CollatzResearch.WordTrace tailWord_848383 prefixEnd_848383 96806279578546540291303 := by
  unfold tailWord_848383
  simp only [CollatzResearch.WordTrace]
  refine ⟨30943070085460758126045803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20628713390307172084030535 30943070085460758126045803)
  ·
    refine ⟨46414605128191137189068705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30943070085460758126045803 46414605128191137189068705)
    ·
      refine ⟨34810953846143352891801529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46414605128191137189068705 34810953846143352891801529)
      ·
        refine ⟨26108215384607514668851147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34810953846143352891801529 26108215384607514668851147)
        ·
          refine ⟨39162323076911272003276721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26108215384607514668851147 39162323076911272003276721)
          ·
            refine ⟨29371742307683454002457541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39162323076911272003276721 29371742307683454002457541)
            ·
              refine ⟨5507201682690647625460789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29371742307683454002457541 5507201682690647625460789)
              ·
                refine ⟨516300157752248214886949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5507201682690647625460789 516300157752248214886949)
                ·
                  refine ⟨96806279578546540291303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 516300157752248214886949 96806279578546540291303)
                  ·
                    rfl

theorem cell22_848383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 4].length) (baseStart_848383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848383 prefixEnd_848383 := by exact prefixLift 848383
  have htrace : WordTrace (prefixWord ++ tailWord_848383) baseStart_848383 baseEnd_848383 := by
    simpa [prefixWord, tailWord_848383, baseEnd_848383] using wordTrace_append hprefix tailTrace_848383
  have hstable : (prefixWord ++ tailWord_848383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848383).length < 2 ^ (prefixWord ++ tailWord_848383).sum := by decide
  have hdescent : baseEnd_848383 < baseStart_848383 := by decide
  rcases family_descends (prefixWord ++ tailWord_848383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848430 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_848430 : Nat := 118140960795 + 848430 * 2 ^ 59
def prefixEnd_848430 : Nat := 4983230072969 + 3 ^ 40 * 848430 * 2
def baseEnd_848430 : Nat := 290434927796147164948765

theorem tailTrace_848430 : CollatzResearch.WordTrace tailWord_848430 prefixEnd_848430 290434927796147164948765 := by
  unfold tailWord_848430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3868098039536310644125843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20629856210860323435337829 3868098039536310644125843)
  ·
    refine ⟨5802147059304465966188765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3868098039536310644125843 5802147059304465966188765)
    ·
      refine ⟨2175805147239174737320787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5802147059304465966188765 2175805147239174737320787)
      ·
        refine ⟨3263707720858762105981181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2175805147239174737320787 3263707720858762105981181)
        ·
          refine ⟨1223890395322035789742943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3263707720858762105981181 1223890395322035789742943)
          ·
            refine ⟨1835835592983053684614415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1223890395322035789742943 1835835592983053684614415)
            ·
              refine ⟨2753753389474580526921623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835835592983053684614415 2753753389474580526921623)
              ·
                refine ⟨4130630084211870790382435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753753389474580526921623 4130630084211870790382435)
                ·
                  refine ⟨6195945126317806185573653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4130630084211870790382435 6195945126317806185573653)
                  ·
                    refine ⟨290434927796147164948765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6195945126317806185573653 290434927796147164948765)
                    ·
                      rfl

theorem cell22_848430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_848430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848430 prefixEnd_848430 := by exact prefixLift 848430
  have htrace : WordTrace (prefixWord ++ tailWord_848430) baseStart_848430 baseEnd_848430 := by
    simpa [prefixWord, tailWord_848430, baseEnd_848430] using wordTrace_append hprefix tailTrace_848430
  have hstable : (prefixWord ++ tailWord_848430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848430).length < 2 ^ (prefixWord ++ tailWord_848430).sum := by decide
  have hdescent : baseEnd_848430 < baseStart_848430 := by decide
  rcases family_descends (prefixWord ++ tailWord_848430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848436 : List Nat := [2, 5, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_848436 : Nat := 118140960795 + 848436 * 2 ^ 59
def prefixEnd_848436 : Nat := 4983230072969 + 3 ^ 40 * 848436 * 2
def baseEnd_848436 : Nat := 290436981718765149298747

theorem tailTrace_848436 : CollatzResearch.WordTrace tailWord_848436 prefixEnd_848436 290436981718765149298747 := by
  unfold tailWord_848436
  simp only [CollatzResearch.WordTrace]
  refine ⟨15472501577134374088862581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20630002102845832118483441 15472501577134374088862581)
  ·
    refine ⟨1450547022856347570830867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15472501577134374088862581 1450547022856347570830867)
    ·
      refine ⟨2175820534284521356246301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1450547022856347570830867 2175820534284521356246301)
      ·
        refine ⟨815932700356695508592363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2175820534284521356246301 815932700356695508592363)
        ·
          refine ⟨1223899050535043262888545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815932700356695508592363 1223899050535043262888545)
          ·
            refine ⟨917924287901282447166409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1223899050535043262888545 917924287901282447166409)
            ·
              refine ⟨688443215925961835374807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 917924287901282447166409 688443215925961835374807)
              ·
                refine ⟨1032664823888942753062211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688443215925961835374807 1032664823888942753062211)
                ·
                  refine ⟨1548997235833414129593317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1032664823888942753062211 1548997235833414129593317)
                  ·
                    refine ⟨290436981718765149298747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1548997235833414129593317 290436981718765149298747)
                    ·
                      rfl

theorem cell22_848436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_848436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848436 prefixEnd_848436 := by exact prefixLift 848436
  have htrace : WordTrace (prefixWord ++ tailWord_848436) baseStart_848436 baseEnd_848436 := by
    simpa [prefixWord, tailWord_848436, baseEnd_848436] using wordTrace_append hprefix tailTrace_848436
  have hstable : (prefixWord ++ tailWord_848436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848436).length < 2 ^ (prefixWord ++ tailWord_848436).sum := by decide
  have hdescent : baseEnd_848436 < baseStart_848436 := by decide
  rcases family_descends (prefixWord ++ tailWord_848436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848460 : List Nat := [2, 2, 1, 3, 1, 2, 4, 1, 3, 3]
def baseStart_848460 : Nat := 118140960795 + 848460 * 2 ^ 59
def prefixEnd_848460 : Nat := 4983230072969 + 3 ^ 40 * 848460 * 2
def baseEnd_848460 : Nat := 290445197409237086698673

theorem tailTrace_848460 : CollatzResearch.WordTrace tailWord_848460 prefixEnd_848460 290445197409237086698673 := by
  unfold tailWord_848460
  simp only [CollatzResearch.WordTrace]
  refine ⟨15472939253090900138299417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20630585670787866851065889 15472939253090900138299417)
  ·
    refine ⟨11604704439818175103724563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15472939253090900138299417 11604704439818175103724563)
    ·
      refine ⟨17407056659727262655586845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11604704439818175103724563 17407056659727262655586845)
      ·
        refine ⟨6527646247397723495845067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17407056659727262655586845 6527646247397723495845067)
        ·
          refine ⟨9791469371096585243767601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6527646247397723495845067 9791469371096585243767601)
          ·
            refine ⟨7343602028322438932825701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9791469371096585243767601 7343602028322438932825701)
            ·
              refine ⟨1376925380310457299904819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7343602028322438932825701 1376925380310457299904819)
              ·
                refine ⟨2065388070465685949857229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1376925380310457299904819 2065388070465685949857229)
                ·
                  refine ⟨774520526424632231196461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2065388070465685949857229 774520526424632231196461)
                  ·
                    refine ⟨290445197409237086698673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 774520526424632231196461 290445197409237086698673)
                    ·
                      rfl

theorem cell22_848460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_848460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848460 prefixEnd_848460 := by exact prefixLift 848460
  have htrace : WordTrace (prefixWord ++ tailWord_848460) baseStart_848460 baseEnd_848460 := by
    simpa [prefixWord, tailWord_848460, baseEnd_848460] using wordTrace_append hprefix tailTrace_848460
  have hstable : (prefixWord ++ tailWord_848460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848460).length < 2 ^ (prefixWord ++ tailWord_848460).sum := by decide
  have hdescent : baseEnd_848460 < baseStart_848460 := by decide
  rcases family_descends (prefixWord ++ tailWord_848460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848494 : List Nat := [4, 1, 2, 2, 2, 1, 3, 3, 1, 3]
def baseStart_848494 : Nat := 118140960795 + 848494 * 2 ^ 59
def prefixEnd_848494 : Nat := 4983230072969 + 3 ^ 40 * 848494 * 2
def baseEnd_848494 : Nat := 290456836304072331348569

theorem tailTrace_848494 : CollatzResearch.WordTrace tailWord_848494 prefixEnd_848494 290456836304072331348569 := by
  unfold tailWord_848494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3868389823507328010417067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20631412392039082722224357 3868389823507328010417067)
  ·
    refine ⟨5802584735260992015625601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3868389823507328010417067 5802584735260992015625601)
    ·
      refine ⟨4351938551445744011719201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5802584735260992015625601 4351938551445744011719201)
      ·
        refine ⟨3263953913584308008789401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4351938551445744011719201 3263953913584308008789401)
        ·
          refine ⟨2447965435188231006592051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3263953913584308008789401 2447965435188231006592051)
          ·
            refine ⟨3671948152782346509888077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2447965435188231006592051 3671948152782346509888077)
            ·
              refine ⟨1376980557293379941208029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3671948152782346509888077 1376980557293379941208029)
              ·
                refine ⟨516367708985017477953011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1376980557293379941208029 516367708985017477953011)
                ·
                  refine ⟨774551563477526216929517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516367708985017477953011 774551563477526216929517)
                  ·
                    refine ⟨290456836304072331348569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 774551563477526216929517 290456836304072331348569)
                    ·
                      rfl

theorem cell22_848494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_848494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848494 prefixEnd_848494 := by exact prefixLift 848494
  have htrace : WordTrace (prefixWord ++ tailWord_848494) baseStart_848494 baseEnd_848494 := by
    simpa [prefixWord, tailWord_848494, baseEnd_848494] using wordTrace_append hprefix tailTrace_848494
  have hstable : (prefixWord ++ tailWord_848494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848494).length < 2 ^ (prefixWord ++ tailWord_848494).sum := by decide
  have hdescent : baseEnd_848494 < baseStart_848494 := by decide
  rcases family_descends (prefixWord ++ tailWord_848494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848580 : List Nat := [2, 3, 3, 1, 1, 2, 3, 7]
def baseStart_848580 : Nat := 118140960795 + 848580 * 2 ^ 59
def prefixEnd_848580 : Nat := 4983230072969 + 3 ^ 40 * 848580 * 2
def baseEnd_848580 : Nat := 32276252873510752633145

theorem tailTrace_848580 : CollatzResearch.WordTrace tailWord_848580 prefixEnd_848580 32276252873510752633145 := by
  unfold tailWord_848580
  simp only [CollatzResearch.WordTrace]
  refine ⟨15475127632873530385483597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20633503510498040513978129 15475127632873530385483597)
  ·
    refine ⟨5803172862327573894556349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15475127632873530385483597 5803172862327573894556349)
    ·
      refine ⟨2176189823372840210458631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5803172862327573894556349 2176189823372840210458631)
      ·
        refine ⟨3264284735059260315687947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2176189823372840210458631 3264284735059260315687947)
        ·
          refine ⟨4896427102588890473531921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3264284735059260315687947 4896427102588890473531921)
          ·
            refine ⟨3672320326941667855148941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4896427102588890473531921 3672320326941667855148941)
            ·
              refine ⟨1377120122603125445680853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3672320326941667855148941 1377120122603125445680853)
              ·
                refine ⟨32276252873510752633145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1377120122603125445680853 32276252873510752633145)
                ·
                  rfl

theorem cell22_848580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 7].length) (baseStart_848580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848580 prefixEnd_848580 := by exact prefixLift 848580
  have htrace : WordTrace (prefixWord ++ tailWord_848580) baseStart_848580 baseEnd_848580 := by
    simpa [prefixWord, tailWord_848580, baseEnd_848580] using wordTrace_append hprefix tailTrace_848580
  have hstable : (prefixWord ++ tailWord_848580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848580).length < 2 ^ (prefixWord ++ tailWord_848580).sum := by decide
  have hdescent : baseEnd_848580 < baseStart_848580 := by decide
  rcases family_descends (prefixWord ++ tailWord_848580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848593 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 2, 6]
def baseStart_848593 : Nat := 118140960795 + 848593 * 2 ^ 59
def prefixEnd_848593 : Nat := 4983230072969 + 3 ^ 40 * 848593 * 2
def baseEnd_848593 : Nat := 290490726027269073123265

theorem tailTrace_848593 : CollatzResearch.WordTrace tailWord_848593 prefixEnd_848593 290490726027269073123265 := by
  unfold tailWord_848593
  simp only [CollatzResearch.WordTrace]
  refine ⟨30950729414699963991190433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20633819609799975994126955 30950729414699963991190433)
  ·
    refine ⟨23213047061024972993392825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30950729414699963991190433 23213047061024972993392825)
    ·
      refine ⟨17409785295768729745044619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23213047061024972993392825 17409785295768729745044619)
      ·
        refine ⟨26114677943653094617566929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17409785295768729745044619 26114677943653094617566929)
        ·
          refine ⟨19586008457739820963175197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26114677943653094617566929 19586008457739820963175197)
          ·
            refine ⟨7344753171652432861190699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19586008457739820963175197 7344753171652432861190699)
            ·
              refine ⟨11017129757478649291786049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7344753171652432861190699 11017129757478649291786049)
              ·
                refine ⟨8262847318108986968839537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11017129757478649291786049 8262847318108986968839537)
                ·
                  refine ⟨6197135488581740226629653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8262847318108986968839537 6197135488581740226629653)
                  ·
                    refine ⟨290490726027269073123265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6197135488581740226629653 290490726027269073123265)
                    ·
                      rfl

theorem cell22_848593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_848593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848593 prefixEnd_848593 := by exact prefixLift 848593
  have htrace : WordTrace (prefixWord ++ tailWord_848593) baseStart_848593 baseEnd_848593 := by
    simpa [prefixWord, tailWord_848593, baseEnd_848593] using wordTrace_append hprefix tailTrace_848593
  have hstable : (prefixWord ++ tailWord_848593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848593).length < 2 ^ (prefixWord ++ tailWord_848593).sum := by decide
  have hdescent : baseEnd_848593 < baseStart_848593 := by decide
  rcases family_descends (prefixWord ++ tailWord_848593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848608 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 7]
def baseStart_848608 : Nat := 118140960795 + 848608 * 2 ^ 59
def prefixEnd_848608 : Nat := 4983230072969 + 3 ^ 40 * 848608 * 2
def baseEnd_848608 : Nat := 96831953611271344666073

theorem tailTrace_848608 : CollatzResearch.WordTrace tailWord_848608 prefixEnd_848608 96831953611271344666073 := by
  unfold tailWord_848608
  simp only [CollatzResearch.WordTrace]
  refine ⟨15475638254822810776493239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20634184339763747701990985 15475638254822810776493239)
  ·
    refine ⟨23213457382234216164739859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15475638254822810776493239 23213457382234216164739859)
    ·
      refine ⟨34820186073351324247109789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23213457382234216164739859 34820186073351324247109789)
      ·
        refine ⟨13057569777506746592666171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34820186073351324247109789 13057569777506746592666171)
        ·
          refine ⟨19586354666260119888999257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13057569777506746592666171 19586354666260119888999257)
          ·
            refine ⟨14689765999695089916749443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19586354666260119888999257 14689765999695089916749443)
            ·
              refine ⟨22034648999542634875124165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14689765999695089916749443 22034648999542634875124165)
              ·
                refine ⟨4131496687414244039085781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22034648999542634875124165 4131496687414244039085781)
                ·
                  refine ⟨96831953611271344666073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4131496687414244039085781 96831953611271344666073)
                  ·
                    rfl

theorem cell22_848608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 7].length) (baseStart_848608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848608 prefixEnd_848608 := by exact prefixLift 848608
  have htrace : WordTrace (prefixWord ++ tailWord_848608) baseStart_848608 baseEnd_848608 := by
    simpa [prefixWord, tailWord_848608, baseEnd_848608] using wordTrace_append hprefix tailTrace_848608
  have hstable : (prefixWord ++ tailWord_848608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848608).length < 2 ^ (prefixWord ++ tailWord_848608).sum := by decide
  have hdescent : baseEnd_848608 < baseStart_848608 := by decide
  rcases family_descends (prefixWord ++ tailWord_848608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848663 : List Nat := [1, 1, 3, 4, 4, 1, 1, 3, 1, 3]
def baseStart_848663 : Nat := 118140960795 + 848663 * 2 ^ 59
def prefixEnd_848663 : Nat := 4983230072969 + 3 ^ 40 * 848663 * 2
def baseEnd_848663 : Nat := 290514688457812223873051

theorem tailTrace_848663 : CollatzResearch.WordTrace tailWord_848663 prefixEnd_848663 290514688457812223873051 := by
  unfold tailWord_848663
  simp only [CollatzResearch.WordTrace]
  refine ⟨30953282524446365946238643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20635521682964243964159095 30953282524446365946238643)
  ·
    refine ⟨46429923786669548919357965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30953282524446365946238643 46429923786669548919357965)
    ·
      refine ⟨17411221420001080844759237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46429923786669548919357965 17411221420001080844759237)
      ·
        refine ⟨3264604016250202658392357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17411221420001080844759237 3264604016250202658392357)
        ·
          refine ⟨612113253046912998448567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3264604016250202658392357 612113253046912998448567)
          ·
            refine ⟨918169879570369497672851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612113253046912998448567 918169879570369497672851)
            ·
              refine ⟨1377254819355554246509277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918169879570369497672851 1377254819355554246509277)
              ·
                refine ⟨516470557258332842440979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1377254819355554246509277 516470557258332842440979)
                ·
                  refine ⟨774705835887499263661469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516470557258332842440979 774705835887499263661469)
                  ·
                    refine ⟨290514688457812223873051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 774705835887499263661469 290514688457812223873051)
                    ·
                      rfl

theorem cell22_848663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 1, 3].length) (baseStart_848663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848663 prefixEnd_848663 := by exact prefixLift 848663
  have htrace : WordTrace (prefixWord ++ tailWord_848663) baseStart_848663 baseEnd_848663 := by
    simpa [prefixWord, tailWord_848663, baseEnd_848663] using wordTrace_append hprefix tailTrace_848663
  have hstable : (prefixWord ++ tailWord_848663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848663).length < 2 ^ (prefixWord ++ tailWord_848663).sum := by decide
  have hdescent : baseEnd_848663 < baseStart_848663 := by decide
  rcases family_descends (prefixWord ++ tailWord_848663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848672 : List Nat := [2, 1, 1, 5, 1, 2, 2, 3, 1, 4]
def baseStart_848672 : Nat := 118140960795 + 848672 * 2 ^ 59
def prefixEnd_848672 : Nat := 4983230072969 + 3 ^ 40 * 848672 * 2
def baseEnd_848672 : Nat := 290517769341739200398023

theorem tailTrace_848672 : CollatzResearch.WordTrace tailWord_848672 prefixEnd_848672 290517769341739200398023 := by
  unfold tailWord_848672
  simp only [CollatzResearch.WordTrace]
  refine ⟨15476805390706880241658135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20635740520942506988877513 15476805390706880241658135)
  ·
    refine ⟨23215208086060320362487203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15476805390706880241658135 23215208086060320362487203)
    ·
      refine ⟨34822812129090480543730805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23215208086060320362487203 34822812129090480543730805)
      ·
        refine ⟨3264638637102232550974763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34822812129090480543730805 3264638637102232550974763)
        ·
          refine ⟨4896957955653348826462145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3264638637102232550974763 4896957955653348826462145)
          ·
            refine ⟨3672718466740011619846609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4896957955653348826462145 3672718466740011619846609)
            ·
              refine ⟨2754538850055008714884957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3672718466740011619846609 2754538850055008714884957)
              ·
                refine ⟨1032952068770628268081859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2754538850055008714884957 1032952068770628268081859)
                ·
                  refine ⟨1549428103155942402122789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1032952068770628268081859 1549428103155942402122789)
                  ·
                    refine ⟨290517769341739200398023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1549428103155942402122789 290517769341739200398023)
                    ·
                      rfl

theorem cell22_848672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 1, 4].length) (baseStart_848672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848672 prefixEnd_848672 := by exact prefixLift 848672
  have htrace : WordTrace (prefixWord ++ tailWord_848672) baseStart_848672 baseEnd_848672 := by
    simpa [prefixWord, tailWord_848672, baseEnd_848672] using wordTrace_append hprefix tailTrace_848672
  have hstable : (prefixWord ++ tailWord_848672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848672).length < 2 ^ (prefixWord ++ tailWord_848672).sum := by decide
  have hdescent : baseEnd_848672 < baseStart_848672 := by decide
  rcases family_descends (prefixWord ++ tailWord_848672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848700 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 6, 4]
def baseStart_848700 : Nat := 118140960795 + 848700 * 2 ^ 59
def prefixEnd_848700 : Nat := 4983230072969 + 3 ^ 40 * 848700 * 2
def baseEnd_848700 : Nat := 290527354313956460697937

theorem tailTrace_848700 : CollatzResearch.WordTrace tailWord_848700 prefixEnd_848700 290527354313956460697937 := by
  unfold tailWord_848700
  simp only [CollatzResearch.WordTrace]
  refine ⟨15477316012656160632667777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20636421350208214176890369 15477316012656160632667777)
  ·
    refine ⟨11607987009492120474500833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15477316012656160632667777 11607987009492120474500833)
    ·
      refine ⟨8705990257119090355875625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11607987009492120474500833 8705990257119090355875625)
      ·
        refine ⟨6529492692839317766906719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8705990257119090355875625 6529492692839317766906719)
        ·
          refine ⟨9794239039258976650360079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6529492692839317766906719 9794239039258976650360079)
          ·
            refine ⟨14691358558888464975540119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9794239039258976650360079 14691358558888464975540119)
            ·
              refine ⟨22037037838332697463310179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14691358558888464975540119 22037037838332697463310179)
              ·
                refine ⟨33055556757499046194965269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22037037838332697463310179 33055556757499046194965269)
                ·
                  refine ⟨1549479223007767790388997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33055556757499046194965269 1549479223007767790388997)
                  ·
                    refine ⟨290527354313956460697937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1549479223007767790388997 290527354313956460697937)
                    ·
                      rfl

theorem cell22_848700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_848700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848700 prefixEnd_848700 := by exact prefixLift 848700
  have htrace : WordTrace (prefixWord ++ tailWord_848700) baseStart_848700 baseEnd_848700 := by
    simpa [prefixWord, tailWord_848700, baseEnd_848700] using wordTrace_append hprefix tailTrace_848700
  have hstable : (prefixWord ++ tailWord_848700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848700).length < 2 ^ (prefixWord ++ tailWord_848700).sum := by decide
  have hdescent : baseEnd_848700 < baseStart_848700 := by decide
  rcases family_descends (prefixWord ++ tailWord_848700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848738 : List Nat := [3, 3, 2, 1, 3, 2, 2, 2, 4]
def baseStart_848738 : Nat := 118140960795 + 848738 * 2 ^ 59
def prefixEnd_848738 : Nat := 4983230072969 + 3 ^ 40 * 848738 * 2
def baseEnd_848738 : Nat := 96846787496845676082607

theorem tailTrace_848738 : CollatzResearch.WordTrace tailWord_848738 prefixEnd_848738 96846787496845676082607 := by
  unfold tailWord_848738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7739004499793663438804717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20637345332783102503479245 7739004499793663438804717)
  ·
    refine ⟨2902126687422623789551769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7739004499793663438804717 2902126687422623789551769)
    ·
      refine ⟨2176595015566967842163827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2902126687422623789551769 2176595015566967842163827)
      ·
        refine ⟨3264892523350451763245741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2176595015566967842163827 3264892523350451763245741)
        ·
          refine ⟨1224334696256419411217153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3264892523350451763245741 1224334696256419411217153)
          ·
            refine ⟨918251022192314558412865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1224334696256419411217153 918251022192314558412865)
            ·
              refine ⟨688688266644235918809649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 918251022192314558412865 688688266644235918809649)
              ·
                refine ⟨516516199983176939107237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688688266644235918809649 516516199983176939107237)
                ·
                  refine ⟨96846787496845676082607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 516516199983176939107237 96846787496845676082607)
                  ·
                    rfl

theorem cell22_848738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_848738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848738 prefixEnd_848738 := by exact prefixLift 848738
  have htrace : WordTrace (prefixWord ++ tailWord_848738) baseStart_848738 baseEnd_848738 := by
    simpa [prefixWord, tailWord_848738, baseEnd_848738] using wordTrace_append hprefix tailTrace_848738
  have hstable : (prefixWord ++ tailWord_848738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848738).length < 2 ^ (prefixWord ++ tailWord_848738).sum := by decide
  have hdescent : baseEnd_848738 < baseStart_848738 := by decide
  rcases family_descends (prefixWord ++ tailWord_848738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848766 : List Nat := [4, 2, 3, 1, 2, 1, 3, 6]
def baseStart_848766 : Nat := 118140960795 + 848766 * 2 ^ 59
def prefixEnd_848766 : Nat := 4983230072969 + 3 ^ 40 * 848766 * 2
def baseEnd_848766 : Nat := 32283327495861587616415

theorem tailTrace_848766 : CollatzResearch.WordTrace tailWord_848766 prefixEnd_848766 32283327495861587616415 := by
  unfold tailWord_848766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3869629905384151817154769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20638026162048809691492101 3869629905384151817154769)
  ·
    refine ⟨2902222429038113862866077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3869629905384151817154769 2902222429038113862866077)
    ·
      refine ⟨1088333410889292698574779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2902222429038113862866077 1088333410889292698574779)
      ·
        refine ⟨1632500116333939047862169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1088333410889292698574779 1632500116333939047862169)
        ·
          refine ⟨1224375087250454285896627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1632500116333939047862169 1224375087250454285896627)
          ·
            refine ⟨1836562630875681428844941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224375087250454285896627 1836562630875681428844941)
            ·
              refine ⟨688710986578380535816853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1836562630875681428844941 688710986578380535816853)
              ·
                refine ⟨32283327495861587616415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 688710986578380535816853 32283327495861587616415)
                ·
                  rfl

theorem cell22_848766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_848766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848766 prefixEnd_848766 := by exact prefixLift 848766
  have htrace : WordTrace (prefixWord ++ tailWord_848766) baseStart_848766 baseEnd_848766 := by
    simpa [prefixWord, tailWord_848766, baseEnd_848766] using wordTrace_append hprefix tailTrace_848766
  have hstable : (prefixWord ++ tailWord_848766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848766).length < 2 ^ (prefixWord ++ tailWord_848766).sum := by decide
  have hdescent : baseEnd_848766 < baseStart_848766 := by decide
  rcases family_descends (prefixWord ++ tailWord_848766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848824 : List Nat := [2, 1, 2, 1, 2, 5, 2, 2, 1, 4]
def baseStart_848824 : Nat := 118140960795 + 848824 * 2 ^ 59
def prefixEnd_848824 : Nat := 4983230072969 + 3 ^ 40 * 848824 * 2
def baseEnd_848824 : Nat := 290569802048061470597557

theorem tailTrace_848824 : CollatzResearch.WordTrace tailWord_848824 prefixEnd_848824 290569802048061470597557 := by
  unfold tailWord_848824
  simp only [CollatzResearch.WordTrace]
  refine ⟨15479577338431545221424763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20639436451242060295233017 15479577338431545221424763)
  ·
    refine ⟨23219366007647317832137145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15479577338431545221424763 23219366007647317832137145)
    ·
      refine ⟨17414524505735488374102859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23219366007647317832137145 17414524505735488374102859)
      ·
        refine ⟨26121786758603232561154289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17414524505735488374102859 26121786758603232561154289)
        ·
          refine ⟨19591340068952424420865717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26121786758603232561154289 19591340068952424420865717)
          ·
            refine ⟨1836688131464289789456161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19591340068952424420865717 1836688131464289789456161)
            ·
              refine ⟨1377516098598217342092121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1836688131464289789456161 1377516098598217342092121)
              ·
                refine ⟨1033137073948663006569091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1377516098598217342092121 1033137073948663006569091)
                ·
                  refine ⟨1549705610922994509853637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033137073948663006569091 1549705610922994509853637)
                  ·
                    refine ⟨290569802048061470597557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1549705610922994509853637 290569802048061470597557)
                    ·
                      rfl

theorem cell22_848824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_848824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848824 prefixEnd_848824 := by exact prefixLift 848824
  have htrace : WordTrace (prefixWord ++ tailWord_848824) baseStart_848824 baseEnd_848824 := by
    simpa [prefixWord, tailWord_848824, baseEnd_848824] using wordTrace_append hprefix tailTrace_848824
  have hstable : (prefixWord ++ tailWord_848824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848824).length < 2 ^ (prefixWord ++ tailWord_848824).sum := by decide
  have hdescent : baseEnd_848824 < baseStart_848824 := by decide
  rcases family_descends (prefixWord ++ tailWord_848824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848839 : List Nat := [1, 1, 4, 1, 1, 2, 5, 3, 4]
def baseStart_848839 : Nat := 118140960795 + 848839 * 2 ^ 59
def prefixEnd_848839 : Nat := 4983230072969 + 3 ^ 40 * 848839 * 2
def baseEnd_848839 : Nat := 96858312284868810490837

theorem tailTrace_848839 : CollatzResearch.WordTrace tailWord_848839 prefixEnd_848839 96858312284868810490837 := by
  unfold tailWord_848839
  simp only [CollatzResearch.WordTrace]
  refine ⟨30959701771808748004645571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20639801181205832003097047 30959701771808748004645571)
  ·
    refine ⟨46439552657713122006968357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30959701771808748004645571 46439552657713122006968357)
    ·
      refine ⟨8707416123321210376306567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46439552657713122006968357 8707416123321210376306567)
      ·
        refine ⟨13061124184981815564459851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8707416123321210376306567 13061124184981815564459851)
        ·
          refine ⟨19591686277472723346689777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13061124184981815564459851 19591686277472723346689777)
          ·
            refine ⟨14693764708104542510017333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19591686277472723346689777 14693764708104542510017333)
            ·
              refine ⟨1377540441384800860314125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14693764708104542510017333 1377540441384800860314125)
              ·
                refine ⟨516577665519300322617797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1377540441384800860314125 516577665519300322617797)
                ·
                  refine ⟨96858312284868810490837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 516577665519300322617797 96858312284868810490837)
                  ·
                    rfl

theorem cell22_848839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 4].length) (baseStart_848839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848839 prefixEnd_848839 := by exact prefixLift 848839
  have htrace : WordTrace (prefixWord ++ tailWord_848839) baseStart_848839 baseEnd_848839 := by
    simpa [prefixWord, tailWord_848839, baseEnd_848839] using wordTrace_append hprefix tailTrace_848839
  have hstable : (prefixWord ++ tailWord_848839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848839).length < 2 ^ (prefixWord ++ tailWord_848839).sum := by decide
  have hdescent : baseEnd_848839 < baseStart_848839 := by decide
  rcases family_descends (prefixWord ++ tailWord_848839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848856 : List Nat := [2, 1, 2, 2, 2, 4, 3, 2, 4]
def baseStart_848856 : Nat := 118140960795 + 848856 * 2 ^ 59
def prefixEnd_848856 : Nat := 4983230072969 + 3 ^ 40 * 848856 * 2
def baseEnd_848856 : Nat := 96860252100674684599153

theorem tailTrace_848856 : CollatzResearch.WordTrace tailWord_848856 prefixEnd_848856 96860252100674684599153 := by
  unfold tailWord_848856
  simp only [CollatzResearch.WordTrace]
  refine ⟨15480160906373579954007211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20640214541831439938676281 15480160906373579954007211)
  ·
    refine ⟨23220241359560369931010817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15480160906373579954007211 23220241359560369931010817)
    ·
      refine ⟨17415181019670277448258113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23220241359560369931010817 17415181019670277448258113)
      ·
        refine ⟨13061385764752708086193585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17415181019670277448258113 13061385764752708086193585)
        ·
          refine ⟨9796039323564531064645189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13061385764752708086193585 9796039323564531064645189)
          ·
            refine ⟨1836757373168349574620973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9796039323564531064645189 1836757373168349574620973)
            ·
              refine ⟨688784014938131090482865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1836757373168349574620973 688784014938131090482865)
              ·
                refine ⟨516588011203598317862149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688784014938131090482865 516588011203598317862149)
                ·
                  refine ⟨96860252100674684599153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 516588011203598317862149 96860252100674684599153)
                  ·
                    rfl

theorem cell22_848856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 4].length) (baseStart_848856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848856 prefixEnd_848856 := by exact prefixLift 848856
  have htrace : WordTrace (prefixWord ++ tailWord_848856) baseStart_848856 baseEnd_848856 := by
    simpa [prefixWord, tailWord_848856, baseEnd_848856] using wordTrace_append hprefix tailTrace_848856
  have hstable : (prefixWord ++ tailWord_848856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848856).length < 2 ^ (prefixWord ++ tailWord_848856).sum := by decide
  have hdescent : baseEnd_848856 < baseStart_848856 := by decide
  rcases family_descends (prefixWord ++ tailWord_848856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848867 : List Nat := [1, 1, 1, 6, 1, 1, 4, 7]
def baseStart_848867 : Nat := 118140960795 + 848867 * 2 ^ 59
def prefixEnd_848867 : Nat := 4983230072969 + 3 ^ 40 * 848867 * 2
def baseEnd_848867 : Nat := 32287169091869299085825

theorem tailTrace_848867 : CollatzResearch.WordTrace tailWord_848867 prefixEnd_848867 32287169091869299085825 := by
  unfold tailWord_848867
  simp only [CollatzResearch.WordTrace]
  refine ⟨30960723015707308786664855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20640482010471539191109903 30960723015707308786664855)
  ·
    refine ⟨46441084523560963179997283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30960723015707308786664855 46441084523560963179997283)
    ·
      refine ⟨69661626785341444769995925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46441084523560963179997283 69661626785341444769995925)
      ·
        refine ⟨3265388755562880223593559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 69661626785341444769995925 3265388755562880223593559)
        ·
          refine ⟨4898083133344320335390339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3265388755562880223593559 4898083133344320335390339)
          ·
            refine ⟨7347124700016480503085509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4898083133344320335390339 7347124700016480503085509)
            ·
              refine ⟨1377585881253090094328533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7347124700016480503085509 1377585881253090094328533)
              ·
                refine ⟨32287169091869299085825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1377585881253090094328533 32287169091869299085825)
                ·
                  rfl

theorem cell22_848867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 7].length) (baseStart_848867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848867 prefixEnd_848867 := by exact prefixLift 848867
  have htrace : WordTrace (prefixWord ++ tailWord_848867) baseStart_848867 baseEnd_848867 := by
    simpa [prefixWord, tailWord_848867, baseEnd_848867] using wordTrace_append hprefix tailTrace_848867
  have hstable : (prefixWord ++ tailWord_848867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848867).length < 2 ^ (prefixWord ++ tailWord_848867).sum := by decide
  have hdescent : baseEnd_848867 < baseStart_848867 := by decide
  rcases family_descends (prefixWord ++ tailWord_848867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848871 : List Nat := [1, 1, 5, 2, 2, 2, 1, 3, 2, 3]
def baseStart_848871 : Nat := 118140960795 + 848871 * 2 ^ 59
def prefixEnd_848871 : Nat := 4983230072969 + 3 ^ 40 * 848871 * 2
def baseEnd_848871 : Nat := 290585891108569014672413

theorem tailTrace_848871 : CollatzResearch.WordTrace tailWord_848871 prefixEnd_848871 290585891108569014672413 := by
  unfold tailWord_848871
  simp only [CollatzResearch.WordTrace]
  refine ⟨30960868907692817469810467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20640579271795211646540311 30960868907692817469810467)
  ·
    refine ⟨46441303361539226204715701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30960868907692817469810467 46441303361539226204715701)
    ·
      refine ⟨4353872190144302456692097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46441303361539226204715701 4353872190144302456692097)
      ·
        refine ⟨3265404142608226842519073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4353872190144302456692097 3265404142608226842519073)
        ·
          refine ⟨2449053106956170131889305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3265404142608226842519073 2449053106956170131889305)
          ·
            refine ⟨1836789830217127598916979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2449053106956170131889305 1836789830217127598916979)
            ·
              refine ⟨2755184745325691398375469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1836789830217127598916979 2755184745325691398375469)
              ·
                refine ⟨1033194279497134274390801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2755184745325691398375469 1033194279497134274390801)
                ·
                  refine ⟨774895709622850705793101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1033194279497134274390801 774895709622850705793101)
                  ·
                    refine ⟨290585891108569014672413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 774895709622850705793101 290585891108569014672413)
                    ·
                      rfl

theorem cell22_848871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_848871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848871 prefixEnd_848871 := by exact prefixLift 848871
  have htrace : WordTrace (prefixWord ++ tailWord_848871) baseStart_848871 baseEnd_848871 := by
    simpa [prefixWord, tailWord_848871, baseEnd_848871] using wordTrace_append hprefix tailTrace_848871
  have hstable : (prefixWord ++ tailWord_848871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848871).length < 2 ^ (prefixWord ++ tailWord_848871).sum := by decide
  have hdescent : baseEnd_848871 < baseStart_848871 := by decide
  rcases family_descends (prefixWord ++ tailWord_848871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848886 : List Nat := [5, 1, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_848886 : Nat := 118140960795 + 848886 * 2 ^ 59
def prefixEnd_848886 : Nat := 4983230072969 + 3 ^ 40 * 848886 * 2
def baseEnd_848886 : Nat := 290591025915113975547367

theorem tailTrace_848886 : CollatzResearch.WordTrace tailWord_848886 prefixEnd_848886 290591025915113975547367 := by
  unfold tailWord_848886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935088500164904689475407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20640944001758983354404341 1935088500164904689475407)
  ·
    refine ⟨2902632750247357034213111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1935088500164904689475407 2902632750247357034213111)
    ·
      refine ⟨4353949125371035551319667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2902632750247357034213111 4353949125371035551319667)
      ·
        refine ⟨6530923688056553326979501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4353949125371035551319667 6530923688056553326979501)
        ·
          refine ⟨2449096383021207497617313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6530923688056553326979501 2449096383021207497617313)
          ·
            refine ⟨1836822287265905623212985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2449096383021207497617313 1836822287265905623212985)
            ·
              refine ⟨1377616715449429217409739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1836822287265905623212985 1377616715449429217409739)
              ·
                refine ⟨2066425073174143826114609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377616715449429217409739 2066425073174143826114609)
                ·
                  refine ⟨1549818804880607869585957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2066425073174143826114609 1549818804880607869585957)
                  ·
                    refine ⟨290591025915113975547367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1549818804880607869585957 290591025915113975547367)
                    ·
                      rfl

theorem cell22_848886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_848886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848886 prefixEnd_848886 := by exact prefixLift 848886
  have htrace : WordTrace (prefixWord ++ tailWord_848886) baseStart_848886 baseEnd_848886 := by
    simpa [prefixWord, tailWord_848886, baseEnd_848886] using wordTrace_append hprefix tailTrace_848886
  have hstable : (prefixWord ++ tailWord_848886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848886).length < 2 ^ (prefixWord ++ tailWord_848886).sum := by decide
  have hdescent : baseEnd_848886 < baseStart_848886 := by decide
  rcases family_descends (prefixWord ++ tailWord_848886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848927 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 1, 7]
def baseStart_848927 : Nat := 118140960795 + 848927 * 2 ^ 59
def prefixEnd_848927 : Nat := 4983230072969 + 3 ^ 40 * 848927 * 2
def baseEnd_848927 : Nat := 290605061053003535272241

theorem tailTrace_848927 : CollatzResearch.WordTrace tailWord_848927 prefixEnd_848927 290605061053003535272241 := by
  unfold tailWord_848927
  simp only [CollatzResearch.WordTrace]
  refine ⟨30962911395489939033849035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20641940930326626022566023 30962911395489939033849035)
  ·
    refine ⟨46444367093234908550773553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30962911395489939033849035 46444367093234908550773553)
    ·
      refine ⟨34833275319926181413080165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46444367093234908550773553 34833275319926181413080165)
      ·
        refine ⟨6531239122486159014952531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34833275319926181413080165 6531239122486159014952531)
        ·
          refine ⟨9796858683729238522428797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6531239122486159014952531 9796858683729238522428797)
          ·
            refine ⟨3673822006398464445910799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9796858683729238522428797 3673822006398464445910799)
            ·
              refine ⟨5510733009597696668866199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3673822006398464445910799 5510733009597696668866199)
              ·
                refine ⟨8266099514396545003299299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5510733009597696668866199 8266099514396545003299299)
                ·
                  refine ⟨12399149271594817504948949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8266099514396545003299299 12399149271594817504948949)
                  ·
                    refine ⟨290605061053003535272241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12399149271594817504948949 290605061053003535272241)
                    ·
                      rfl

theorem cell22_848927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_848927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848927 prefixEnd_848927 := by exact prefixLift 848927
  have htrace : WordTrace (prefixWord ++ tailWord_848927) baseStart_848927 baseEnd_848927 := by
    simpa [prefixWord, tailWord_848927, baseEnd_848927] using wordTrace_append hprefix tailTrace_848927
  have hstable : (prefixWord ++ tailWord_848927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848927).length < 2 ^ (prefixWord ++ tailWord_848927).sum := by decide
  have hdescent : baseEnd_848927 < baseStart_848927 := by decide
  rcases family_descends (prefixWord ++ tailWord_848927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848929 : List Nat := [1, 2, 3, 2, 3, 1, 2, 3, 5]
def baseStart_848929 : Nat := 118140960795 + 848929 * 2 ^ 59
def prefixEnd_848929 : Nat := 4983230072969 + 3 ^ 40 * 848929 * 2
def baseEnd_848929 : Nat := 96868581897958732240745

theorem tailTrace_848929 : CollatzResearch.WordTrace tailWord_848929 prefixEnd_848929 96868581897958732240745 := by
  unfold tailWord_848929
  simp only [CollatzResearch.WordTrace]
  refine ⟨30962984341482693375421841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20641989560988462250281227 30962984341482693375421841)
  ·
    refine ⟨23222238256112020031566381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30962984341482693375421841 23222238256112020031566381)
    ·
      refine ⟨8708339346042007511837393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23222238256112020031566381 8708339346042007511837393)
      ·
        refine ⟨6531254509531505633878045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8708339346042007511837393 6531254509531505633878045)
        ·
          refine ⟨2449220441074314612704267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6531254509531505633878045 2449220441074314612704267)
          ·
            refine ⟨3673830661611471919056401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2449220441074314612704267 3673830661611471919056401)
            ·
              refine ⟨2755372996208603939292301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3673830661611471919056401 2755372996208603939292301)
              ·
                refine ⟨1033264873578226477234613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2755372996208603939292301 1033264873578226477234613)
                ·
                  refine ⟨96868581897958732240745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1033264873578226477234613 96868581897958732240745)
                  ·
                    rfl

theorem cell22_848929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 5].length) (baseStart_848929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848929 prefixEnd_848929 := by exact prefixLift 848929
  have htrace : WordTrace (prefixWord ++ tailWord_848929) baseStart_848929 baseEnd_848929 := by
    simpa [prefixWord, tailWord_848929, baseEnd_848929] using wordTrace_append hprefix tailTrace_848929
  have hstable : (prefixWord ++ tailWord_848929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848929).length < 2 ^ (prefixWord ++ tailWord_848929).sum := by decide
  have hdescent : baseEnd_848929 < baseStart_848929 := by decide
  rcases family_descends (prefixWord ++ tailWord_848929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848950 : List Nat := [5, 1, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_848950 : Nat := 118140960795 + 848950 * 2 ^ 59
def prefixEnd_848950 : Nat := 4983230072969 + 3 ^ 40 * 848950 * 2
def baseEnd_848950 : Nat := 290612934423039141947171

theorem tailTrace_848950 : CollatzResearch.WordTrace tailWord_848950 prefixEnd_848950 290612934423039141947171 := by
  unfold tailWord_848950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935234392150413372621019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20642500182937742641290869 1935234392150413372621019)
  ·
    refine ⟨2902851588225620058931529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1935234392150413372621019 2902851588225620058931529)
    ·
      refine ⟨2177138691169215044198647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2902851588225620058931529 2177138691169215044198647)
      ·
        refine ⟨3265708036753822566297971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2177138691169215044198647 3265708036753822566297971)
        ·
          refine ⟨4898562055130733849446957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3265708036753822566297971 4898562055130733849446957)
          ·
            refine ⟨1836960770674025193542609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4898562055130733849446957 1836960770674025193542609)
            ·
              refine ⟨1377720578005518895156957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1836960770674025193542609 1377720578005518895156957)
              ·
                refine ⟨516645216752069585683859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1377720578005518895156957 516645216752069585683859)
                ·
                  refine ⟨774967825128104378525789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516645216752069585683859 774967825128104378525789)
                  ·
                    refine ⟨290612934423039141947171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 774967825128104378525789 290612934423039141947171)
                    ·
                      rfl

theorem cell22_848950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_848950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848950 prefixEnd_848950 := by exact prefixLift 848950
  have htrace : WordTrace (prefixWord ++ tailWord_848950) baseStart_848950 baseEnd_848950 := by
    simpa [prefixWord, tailWord_848950, baseEnd_848950] using wordTrace_append hprefix tailTrace_848950
  have hstable : (prefixWord ++ tailWord_848950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848950).length < 2 ^ (prefixWord ++ tailWord_848950).sum := by decide
  have hdescent : baseEnd_848950 < baseStart_848950 := by decide
  rcases family_descends (prefixWord ++ tailWord_848950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848974 : List Nat := [4, 1, 1, 1, 1, 3, 4, 1, 6]
def baseStart_848974 : Nat := 118140960795 + 848974 * 2 ^ 59
def prefixEnd_848974 : Nat := 4983230072969 + 3 ^ 40 * 848974 * 2
def baseEnd_848974 : Nat := 96873716704503693115699

theorem tailTrace_848974 : CollatzResearch.WordTrace tailWord_848974 prefixEnd_848974 96873716704503693115699 := by
  unfold tailWord_848974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3870578203289958257601247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20643083750879777373873317 3870578203289958257601247)
  ·
    refine ⟨5805867304934937386401871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3870578203289958257601247 5805867304934937386401871)
    ·
      refine ⟨8708800957402406079602807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5805867304934937386401871 8708800957402406079602807)
      ·
        refine ⟨13063201436103609119404211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8708800957402406079602807 13063201436103609119404211)
        ·
          refine ⟨19594802154155413679106317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13063201436103609119404211 19594802154155413679106317)
          ·
            refine ⟨7348050807808280129664869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19594802154155413679106317 7348050807808280129664869)
            ·
              refine ⟨1377759526464052524312163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7348050807808280129664869 1377759526464052524312163)
              ·
                refine ⟨2066639289696078786468245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377759526464052524312163 2066639289696078786468245)
                ·
                  refine ⟨96873716704503693115699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2066639289696078786468245 96873716704503693115699)
                  ·
                    rfl

theorem cell22_848974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_848974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_848974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_848974 prefixEnd_848974 := by exact prefixLift 848974
  have htrace : WordTrace (prefixWord ++ tailWord_848974) baseStart_848974 baseEnd_848974 := by
    simpa [prefixWord, tailWord_848974, baseEnd_848974] using wordTrace_append hprefix tailTrace_848974
  have hstable : (prefixWord ++ tailWord_848974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848974).length < 2 ^ (prefixWord ++ tailWord_848974).sum := by decide
  have hdescent : baseEnd_848974 < baseStart_848974 := by decide
  rcases family_descends (prefixWord ++ tailWord_848974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849004 : List Nat := [2, 2, 1, 1, 3, 2, 2, 3, 2, 4]
def baseStart_849004 : Nat := 118140960795 + 849004 * 2 ^ 59
def prefixEnd_849004 : Nat := 4983230072969 + 3 ^ 40 * 849004 * 2
def baseEnd_849004 : Nat := 290631419726601001097005

theorem tailTrace_849004 : CollatzResearch.WordTrace tailWord_849004 prefixEnd_849004 290631419726601001097005 := by
  unfold tailWord_849004
  simp only [CollatzResearch.WordTrace]
  refine ⟨15482859908105490592201033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20643813210807320789601377 15482859908105490592201033)
  ·
    refine ⟨11612144931079117944150775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15482859908105490592201033 11612144931079117944150775)
    ·
      refine ⟨17418217396618676916226163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11612144931079117944150775 17418217396618676916226163)
      ·
        refine ⟨26127326094928015374339245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17418217396618676916226163 26127326094928015374339245)
        ·
          refine ⟨9797747285598005765377217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26127326094928015374339245 9797747285598005765377217)
          ·
            refine ⟨7348310464198504324032913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9797747285598005765377217 7348310464198504324032913)
            ·
              refine ⟨5511232848148878243024685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7348310464198504324032913 5511232848148878243024685)
              ·
                refine ⟨2066712318055829341134257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5511232848148878243024685 2066712318055829341134257)
                ·
                  refine ⟨1550034238541872005850693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2066712318055829341134257 1550034238541872005850693)
                  ·
                    refine ⟨290631419726601001097005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1550034238541872005850693 290631419726601001097005)
                    ·
                      rfl

theorem cell22_849004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_849004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849004 prefixEnd_849004 := by exact prefixLift 849004
  have htrace : WordTrace (prefixWord ++ tailWord_849004) baseStart_849004 baseEnd_849004 := by
    simpa [prefixWord, tailWord_849004, baseEnd_849004] using wordTrace_append hprefix tailTrace_849004
  have hstable : (prefixWord ++ tailWord_849004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849004).length < 2 ^ (prefixWord ++ tailWord_849004).sum := by decide
  have hdescent : baseEnd_849004 < baseStart_849004 := by decide
  rcases family_descends (prefixWord ++ tailWord_849004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849006 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 4, 3]
def baseStart_849006 : Nat := 118140960795 + 849006 * 2 ^ 59
def prefixEnd_849006 : Nat := 4983230072969 + 3 ^ 40 * 849006 * 2
def baseEnd_849006 : Nat := 290632104367473662546999

theorem tailTrace_849006 : CollatzResearch.WordTrace tailWord_849006 prefixEnd_849006 290632104367473662546999 := by
  unfold tailWord_849006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3870724095275466940746859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20643861841469157017316581 3870724095275466940746859)
  ·
    refine ⟨5806086142913200411120289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3870724095275466940746859 5806086142913200411120289)
    ·
      refine ⟨4354564607184900308340217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5806086142913200411120289 4354564607184900308340217)
      ·
        refine ⟨3265923455388675231255163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4354564607184900308340217 3265923455388675231255163)
        ·
          refine ⟨4898885183083012846882745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3265923455388675231255163 4898885183083012846882745)
          ·
            refine ⟨3674163887312259635162059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4898885183083012846882745 3674163887312259635162059)
            ·
              refine ⟨5511245830968389452743089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674163887312259635162059 5511245830968389452743089)
              ·
                refine ⟨4133434373226292089557317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5511245830968389452743089 4133434373226292089557317)
                ·
                  refine ⟨775018944979929766791997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4133434373226292089557317 775018944979929766791997)
                  ·
                    refine ⟨290632104367473662546999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 775018944979929766791997 290632104367473662546999)
                    ·
                      rfl

theorem cell22_849006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_849006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849006 prefixEnd_849006 := by exact prefixLift 849006
  have htrace : WordTrace (prefixWord ++ tailWord_849006) baseStart_849006 baseEnd_849006 := by
    simpa [prefixWord, tailWord_849006, baseEnd_849006] using wordTrace_append hprefix tailTrace_849006
  have hstable : (prefixWord ++ tailWord_849006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849006).length < 2 ^ (prefixWord ++ tailWord_849006).sum := by decide
  have hdescent : baseEnd_849006 < baseStart_849006 := by decide
  rcases family_descends (prefixWord ++ tailWord_849006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849079 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 2, 5]
def baseStart_849079 : Nat := 118140960795 + 849079 * 2 ^ 59
def prefixEnd_849079 : Nat := 4983230072969 + 3 ^ 40 * 849079 * 2
def baseEnd_849079 : Nat := 290657093759325805471775

theorem tailTrace_849079 : CollatzResearch.WordTrace tailWord_849079 prefixEnd_849079 290657093759325805471775 := by
  unfold tailWord_849079
  simp only [CollatzResearch.WordTrace]
  refine ⟨30968455290939268993382291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20645636860626179328921527 30968455290939268993382291)
  ·
    refine ⟨46452682936408903490073437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30968455290939268993382291 46452682936408903490073437)
    ·
      refine ⟨17419756101153338808777539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46452682936408903490073437 17419756101153338808777539)
      ·
        refine ⟨26129634151730008213166309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17419756101153338808777539 26129634151730008213166309)
        ·
          refine ⟨4899306403449376539968683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26129634151730008213166309 4899306403449376539968683)
          ·
            refine ⟨7348959605174064809953025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4899306403449376539968683 7348959605174064809953025)
            ·
              refine ⟨5511719703880548607464769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7348959605174064809953025 5511719703880548607464769)
              ·
                refine ⟨4133789777910411455598577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5511719703880548607464769 4133789777910411455598577)
                ·
                  refine ⟨3100342333432808591698933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4133789777910411455598577 3100342333432808591698933)
                  ·
                    refine ⟨290657093759325805471775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3100342333432808591698933 290657093759325805471775)
                    ·
                      rfl

theorem cell22_849079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_849079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849079 prefixEnd_849079 := by exact prefixLift 849079
  have htrace : WordTrace (prefixWord ++ tailWord_849079) baseStart_849079 baseEnd_849079 := by
    simpa [prefixWord, tailWord_849079, baseEnd_849079] using wordTrace_append hprefix tailTrace_849079
  have hstable : (prefixWord ++ tailWord_849079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849079).length < 2 ^ (prefixWord ++ tailWord_849079).sum := by decide
  have hdescent : baseEnd_849079 < baseStart_849079 := by decide
  rcases family_descends (prefixWord ++ tailWord_849079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849081 : List Nat := [1, 2, 1, 4, 1, 4, 2, 2, 5]
def baseStart_849081 : Nat := 118140960795 + 849081 * 2 ^ 59
def prefixEnd_849081 : Nat := 4983230072969 + 3 ^ 40 * 849081 * 2
def baseEnd_849081 : Nat := 96885926133399488973923

theorem tailTrace_849081 : CollatzResearch.WordTrace tailWord_849081 prefixEnd_849081 96885926133399488973923 := by
  unfold tailWord_849081
  simp only [CollatzResearch.WordTrace]
  refine ⟨30968528236932023334955097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20645685491288015556636731 30968528236932023334955097)
  ·
    refine ⟨23226396177699017501216323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30968528236932023334955097 23226396177699017501216323)
    ·
      refine ⟨34839594266548526251824485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23226396177699017501216323 34839594266548526251824485)
      ·
        refine ⟨6532423924977848672217091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34839594266548526251824485 6532423924977848672217091)
        ·
          refine ⟨9798635887466773008325637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6532423924977848672217091 9798635887466773008325637)
          ·
            refine ⟨1837244228900019939061057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9798635887466773008325637 1837244228900019939061057)
            ·
              refine ⟨1377933171675014954295793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1837244228900019939061057 1377933171675014954295793)
              ·
                refine ⟨1033449878756261215721845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1377933171675014954295793 1033449878756261215721845)
                ·
                  refine ⟨96885926133399488973923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1033449878756261215721845 96885926133399488973923)
                  ·
                    rfl

theorem cell22_849081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 5].length) (baseStart_849081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849081 prefixEnd_849081 := by exact prefixLift 849081
  have htrace : WordTrace (prefixWord ++ tailWord_849081) baseStart_849081 baseEnd_849081 := by
    simpa [prefixWord, tailWord_849081, baseEnd_849081] using wordTrace_append hprefix tailTrace_849081
  have hstable : (prefixWord ++ tailWord_849081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849081).length < 2 ^ (prefixWord ++ tailWord_849081).sum := by decide
  have hdescent : baseEnd_849081 < baseStart_849081 := by decide
  rcases family_descends (prefixWord ++ tailWord_849081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849085 : List Nat := [1, 4, 1, 2, 1, 1, 6, 2, 1, 3]
def baseStart_849085 : Nat := 118140960795 + 849085 * 2 ^ 59
def prefixEnd_849085 : Nat := 4983230072969 + 3 ^ 40 * 849085 * 2
def baseEnd_849085 : Nat := 290659147681943789821757

theorem tailTrace_849085 : CollatzResearch.WordTrace tailWord_849085 prefixEnd_849085 290659147681943789821757 := by
  unfold tailWord_849085
  simp only [CollatzResearch.WordTrace]
  refine ⟨30968674128917532018100709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20645782752611688012067139 30968674128917532018100709)
  ·
    refine ⟨5806626399172037253393883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30968674128917532018100709 5806626399172037253393883)
    ·
      refine ⟨8709939598758055880090825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5806626399172037253393883 8709939598758055880090825)
      ·
        refine ⟨6532454699068541910068119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8709939598758055880090825 6532454699068541910068119)
        ·
          refine ⟨9798682048602812865102179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6532454699068541910068119 9798682048602812865102179)
          ·
            refine ⟨14698023072904219297653269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9798682048602812865102179 14698023072904219297653269)
            ·
              refine ⟨688969831542385279577497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14698023072904219297653269 688969831542385279577497)
              ·
                refine ⟨516727373656788959683123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688969831542385279577497 516727373656788959683123)
                ·
                  refine ⟨775091060485183439524685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516727373656788959683123 775091060485183439524685)
                  ·
                    refine ⟨290659147681943789821757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 775091060485183439524685 290659147681943789821757)
                    ·
                      rfl

theorem cell22_849085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_849085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849085 prefixEnd_849085 := by exact prefixLift 849085
  have htrace : WordTrace (prefixWord ++ tailWord_849085) baseStart_849085 baseEnd_849085 := by
    simpa [prefixWord, tailWord_849085, baseEnd_849085] using wordTrace_append hprefix tailTrace_849085
  have hstable : (prefixWord ++ tailWord_849085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849085).length < 2 ^ (prefixWord ++ tailWord_849085).sum := by decide
  have hdescent : baseEnd_849085 < baseStart_849085 := by decide
  rcases family_descends (prefixWord ++ tailWord_849085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849156 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_849156 : Nat := 118140960795 + 849156 * 2 ^ 59
def prefixEnd_849156 : Nat := 4983230072969 + 3 ^ 40 * 849156 * 2
def baseEnd_849156 : Nat := 290683452432923271296539

theorem tailTrace_849156 : CollatzResearch.WordTrace tailWord_849156 prefixEnd_849156 290683452432923271296539 := by
  unfold tailWord_849156
  simp only [CollatzResearch.WordTrace]
  refine ⟨15485631855830155571967661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20647509141106874095956881 15485631855830155571967661)
  ·
    refine ⟨5807111945936308339487873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15485631855830155571967661 5807111945936308339487873)
    ·
      refine ⟨4355333959452231254615905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5807111945936308339487873 4355333959452231254615905)
      ·
        refine ⟨3266500469589173440961929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4355333959452231254615905 3266500469589173440961929)
        ·
          refine ⟨2449875352191880080721447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3266500469589173440961929 2449875352191880080721447)
          ·
            refine ⟨3674813028287820121082171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2449875352191880080721447 3674813028287820121082171)
            ·
              refine ⟨5512219542431730181623257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674813028287820121082171 5512219542431730181623257)
              ·
                refine ⟨4134164656823797636217443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5512219542431730181623257 4134164656823797636217443)
                ·
                  refine ⟨6201246985235696454326165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4134164656823797636217443 6201246985235696454326165)
                  ·
                    refine ⟨290683452432923271296539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6201246985235696454326165 290683452432923271296539)
                    ·
                      rfl

theorem cell22_849156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_849156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849156 prefixEnd_849156 := by exact prefixLift 849156
  have htrace : WordTrace (prefixWord ++ tailWord_849156) baseStart_849156 baseEnd_849156 := by
    simpa [prefixWord, tailWord_849156, baseEnd_849156] using wordTrace_append hprefix tailTrace_849156
  have hstable : (prefixWord ++ tailWord_849156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849156).length < 2 ^ (prefixWord ++ tailWord_849156).sum := by decide
  have hdescent : baseEnd_849156 < baseStart_849156 := by decide
  rcases family_descends (prefixWord ++ tailWord_849156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849169 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 2, 7]
def baseStart_849169 : Nat := 118140960795 + 849169 * 2 ^ 59
def prefixEnd_849169 : Nat := 4983230072969 + 3 ^ 40 * 849169 * 2
def baseEnd_849169 : Nat := 290687902598595570721499

theorem tailTrace_849169 : CollatzResearch.WordTrace tailWord_849169 prefixEnd_849169 290687902598595570721499 := by
  unfold tailWord_849169
  simp only [CollatzResearch.WordTrace]
  refine ⟨30971737860613214364158561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20647825240408809576105707 30971737860613214364158561)
  ·
    refine ⟨23228803395459910773118921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30971737860613214364158561 23228803395459910773118921)
    ·
      refine ⟨17421602546594933079839191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23228803395459910773118921 17421602546594933079839191)
      ·
        refine ⟨26132403819892399619758787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17421602546594933079839191 26132403819892399619758787)
        ·
          refine ⟨39198605729838599429638181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26132403819892399619758787 39198605729838599429638181)
          ·
            refine ⟨7349738574344737393057159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39198605729838599429638181 7349738574344737393057159)
            ·
              refine ⟨11024607861517106089585739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7349738574344737393057159 11024607861517106089585739)
              ·
                refine ⟨16536911792275659134378609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11024607861517106089585739 16536911792275659134378609)
                ·
                  refine ⟨12402683844206744350783957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16536911792275659134378609 12402683844206744350783957)
                  ·
                    refine ⟨290687902598595570721499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12402683844206744350783957 290687902598595570721499)
                    ·
                      rfl

theorem cell22_849169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_849169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849169 prefixEnd_849169 := by exact prefixLift 849169
  have htrace : WordTrace (prefixWord ++ tailWord_849169) baseStart_849169 baseEnd_849169 := by
    simpa [prefixWord, tailWord_849169, baseEnd_849169] using wordTrace_append hprefix tailTrace_849169
  have hstable : (prefixWord ++ tailWord_849169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849169).length < 2 ^ (prefixWord ++ tailWord_849169).sum := by decide
  have hdescent : baseEnd_849169 < baseStart_849169 := by decide
  rcases family_descends (prefixWord ++ tailWord_849169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849203 : List Nat := [1, 1, 1, 2, 5, 2, 3, 1, 3, 3]
def baseStart_849203 : Nat := 118140960795 + 849203 * 2 ^ 59
def prefixEnd_849203 : Nat := 4983230072969 + 3 ^ 40 * 849203 * 2
def baseEnd_849203 : Nat := 290699541493430815371395

theorem tailTrace_849203 : CollatzResearch.WordTrace tailWord_849203 prefixEnd_849203 290699541493430815371395 := by
  unfold tailWord_849203
  simp only [CollatzResearch.WordTrace]
  refine ⟨30972977942490038170896263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20648651961660025447264175 30972977942490038170896263)
  ·
    refine ⟨46459466913735057256344395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30972977942490038170896263 46459466913735057256344395)
    ·
      refine ⟨69689200370602585884516593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46459466913735057256344395 69689200370602585884516593)
      ·
        refine ⟨52266900277951939413387445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69689200370602585884516593 52266900277951939413387445)
        ·
          refine ⟨4900021901057994320005073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52266900277951939413387445 4900021901057994320005073)
          ·
            refine ⟨3675016425793495740003805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4900021901057994320005073 3675016425793495740003805)
            ·
              refine ⟨1378131159672560902501427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3675016425793495740003805 1378131159672560902501427)
              ·
                refine ⟨2067196739508841353752141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378131159672560902501427 2067196739508841353752141)
                ·
                  refine ⟨775198777315815507657053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2067196739508841353752141 775198777315815507657053)
                  ·
                    refine ⟨290699541493430815371395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 775198777315815507657053 290699541493430815371395)
                    ·
                      rfl

theorem cell22_849203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 3].length) (baseStart_849203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849203 prefixEnd_849203 := by exact prefixLift 849203
  have htrace : WordTrace (prefixWord ++ tailWord_849203) baseStart_849203 baseEnd_849203 := by
    simpa [prefixWord, tailWord_849203, baseEnd_849203] using wordTrace_append hprefix tailTrace_849203
  have hstable : (prefixWord ++ tailWord_849203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849203).length < 2 ^ (prefixWord ++ tailWord_849203).sum := by decide
  have hdescent : baseEnd_849203 < baseStart_849203 := by decide
  rcases family_descends (prefixWord ++ tailWord_849203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849209 : List Nat := [1, 2, 1, 6, 3, 1, 2, 1, 2, 3]
def baseStart_849209 : Nat := 118140960795 + 849209 * 2 ^ 59
def prefixEnd_849209 : Nat := 4983230072969 + 3 ^ 40 * 849209 * 2
def baseEnd_849209 : Nat := 290701595416048799721377

theorem tailTrace_849209 : CollatzResearch.WordTrace tailWord_849209 prefixEnd_849209 290701595416048799721377 := by
  unfold tailWord_849209
  simp only [CollatzResearch.WordTrace]
  refine ⟨30973196780468301195614681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20648797853645534130409787 30973196780468301195614681)
  ·
    refine ⟨23229897585351225896711011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30973196780468301195614681 23229897585351225896711011)
    ·
      refine ⟨34844846378026838845066517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23229897585351225896711011 34844846378026838845066517)
      ·
        refine ⟨1633352173970008070862493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34844846378026838845066517 1633352173970008070862493)
        ·
          refine ⟨612507065238753026573435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1633352173970008070862493 612507065238753026573435)
          ·
            refine ⟨918760597858129539860153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612507065238753026573435 918760597858129539860153)
            ·
              refine ⟨689070448393597154895115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 918760597858129539860153 689070448393597154895115)
              ·
                refine ⟨1033605672590395732342673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689070448393597154895115 1033605672590395732342673)
                ·
                  refine ⟨775204254442796799257005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1033605672590395732342673 775204254442796799257005)
                  ·
                    refine ⟨290701595416048799721377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 775204254442796799257005 290701595416048799721377)
                    ·
                      rfl

theorem cell22_849209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 2, 3].length) (baseStart_849209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849209 prefixEnd_849209 := by exact prefixLift 849209
  have htrace : WordTrace (prefixWord ++ tailWord_849209) baseStart_849209 baseEnd_849209 := by
    simpa [prefixWord, tailWord_849209, baseEnd_849209] using wordTrace_append hprefix tailTrace_849209
  have hstable : (prefixWord ++ tailWord_849209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849209).length < 2 ^ (prefixWord ++ tailWord_849209).sum := by decide
  have hdescent : baseEnd_849209 < baseStart_849209 := by decide
  rcases family_descends (prefixWord ++ tailWord_849209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849216 : List Nat := [2, 1, 1, 2, 2, 1, 5, 3, 5]
def baseStart_849216 : Nat := 118140960795 + 849216 * 2 ^ 59
def prefixEnd_849216 : Nat := 4983230072969 + 3 ^ 40 * 849216 * 2
def baseEnd_849216 : Nat := 96901330553034371598785

theorem tailTrace_849216 : CollatzResearch.WordTrace tailWord_849216 prefixEnd_849216 96901330553034371598785 := by
  unfold tailWord_849216
  simp only [CollatzResearch.WordTrace]
  refine ⟨15486726045721470695559751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20648968060961960927413001 15486726045721470695559751)
  ·
    refine ⟨23230089068582206043339627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15486726045721470695559751 23230089068582206043339627)
    ·
      refine ⟨34845133602873309065009441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23230089068582206043339627 34845133602873309065009441)
      ·
        refine ⟨26133850202154981798757081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34845133602873309065009441 26133850202154981798757081)
        ·
          refine ⟨19600387651616236349067811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26133850202154981798757081 19600387651616236349067811)
          ·
            refine ⟨29400581477424354523601717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19600387651616236349067811 29400581477424354523601717)
            ·
              refine ⟨2756304513508533236587661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29400581477424354523601717 2756304513508533236587661)
              ·
                refine ⟨1033614192565699963720373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2756304513508533236587661 1033614192565699963720373)
                ·
                  refine ⟨96901330553034371598785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1033614192565699963720373 96901330553034371598785)
                  ·
                    rfl

theorem cell22_849216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 5].length) (baseStart_849216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849216 prefixEnd_849216 := by exact prefixLift 849216
  have htrace : WordTrace (prefixWord ++ tailWord_849216) baseStart_849216 baseEnd_849216 := by
    simpa [prefixWord, tailWord_849216, baseEnd_849216] using wordTrace_append hprefix tailTrace_849216
  have hstable : (prefixWord ++ tailWord_849216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849216).length < 2 ^ (prefixWord ++ tailWord_849216).sum := by decide
  have hdescent : baseEnd_849216 < baseStart_849216 := by decide
  rcases family_descends (prefixWord ++ tailWord_849216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849291 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 1, 6]
def baseStart_849291 : Nat := 118140960795 + 849291 * 2 ^ 59
def prefixEnd_849291 : Nat := 4983230072969 + 3 ^ 40 * 849291 * 2
def baseEnd_849291 : Nat := 290729665691827919171125

theorem tailTrace_849291 : CollatzResearch.WordTrace tailWord_849291 prefixEnd_849291 290729665691827919171125 := by
  unfold tailWord_849291
  simp only [CollatzResearch.WordTrace]
  refine ⟨30976187566171229200099727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20650791710780819466733151 30976187566171229200099727)
  ·
    refine ⟨46464281349256843800149591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30976187566171229200099727 46464281349256843800149591)
    ·
      refine ⟨69696422023885265700224387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46464281349256843800149591 69696422023885265700224387)
      ·
        refine ⟨104544633035827898550336581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69696422023885265700224387 104544633035827898550336581)
        ·
          refine ⟨19602118694217730978188109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104544633035827898550336581 19602118694217730978188109)
          ·
            refine ⟨7350794510331649116820541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19602118694217730978188109 7350794510331649116820541)
            ·
              refine ⟨2756547941374368418807703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7350794510331649116820541 2756547941374368418807703)
              ·
                refine ⟨4134821912061552628211555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756547941374368418807703 4134821912061552628211555)
                ·
                  refine ⟨6202232868092328942317333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4134821912061552628211555 6202232868092328942317333)
                  ·
                    refine ⟨290729665691827919171125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6202232868092328942317333 290729665691827919171125)
                    ·
                      rfl

theorem cell22_849291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 6].length) (baseStart_849291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849291 prefixEnd_849291 := by exact prefixLift 849291
  have htrace : WordTrace (prefixWord ++ tailWord_849291) baseStart_849291 baseEnd_849291 := by
    simpa [prefixWord, tailWord_849291, baseEnd_849291] using wordTrace_append hprefix tailTrace_849291
  have hstable : (prefixWord ++ tailWord_849291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849291).length < 2 ^ (prefixWord ++ tailWord_849291).sum := by decide
  have hdescent : baseEnd_849291 < baseStart_849291 := by decide
  rcases family_descends (prefixWord ++ tailWord_849291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849306 : List Nat := [3, 1, 1, 4, 1, 1, 11]
def baseStart_849306 : Nat := 118140960795 + 849306 * 2 ^ 59
def prefixEnd_849306 : Nat := 4983230072969 + 3 ^ 40 * 849306 * 2
def baseEnd_849306 : Nat := 10767955574013810372077

theorem tailTrace_849306 : CollatzResearch.WordTrace tailWord_849306 prefixEnd_849306 10767955574013810372077 := by
  unfold tailWord_849306
  simp only [CollatzResearch.WordTrace]
  refine ⟨7744183665279221690473943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20651156440744591174597181 7744183665279221690473943)
  ·
    refine ⟨11616275497918832535710915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7744183665279221690473943 11616275497918832535710915)
    ·
      refine ⟨17424413246878248803566373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11616275497918832535710915 17424413246878248803566373)
      ·
        refine ⟨3267077483789671650668695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17424413246878248803566373 3267077483789671650668695)
        ·
          refine ⟨4900616225684507476003043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3267077483789671650668695 4900616225684507476003043)
          ·
            refine ⟨7350924338526761214004565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4900616225684507476003043 7350924338526761214004565)
            ·
              refine ⟨10767955574013810372077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7350924338526761214004565 10767955574013810372077)
              ·
                rfl

theorem cell22_849306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 11].length) (baseStart_849306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849306 prefixEnd_849306 := by exact prefixLift 849306
  have htrace : WordTrace (prefixWord ++ tailWord_849306) baseStart_849306 baseEnd_849306 := by
    simpa [prefixWord, tailWord_849306, baseEnd_849306] using wordTrace_append hprefix tailTrace_849306
  have hstable : (prefixWord ++ tailWord_849306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849306).length < 2 ^ (prefixWord ++ tailWord_849306).sum := by decide
  have hdescent : baseEnd_849306 < baseStart_849306 := by decide
  rcases family_descends (prefixWord ++ tailWord_849306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849336 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 2, 6]
def baseStart_849336 : Nat := 118140960795 + 849336 * 2 ^ 59
def prefixEnd_849336 : Nat := 4983230072969 + 3 ^ 40 * 849336 * 2
def baseEnd_849336 : Nat := 290745070111462801795987

theorem tailTrace_849336 : CollatzResearch.WordTrace tailWord_849336 prefixEnd_849336 290745070111462801795987 := by
  unfold tailWord_849336
  simp only [CollatzResearch.WordTrace]
  refine ⟨15488914425504100942743931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20651885900672134590325241 15488914425504100942743931)
  ·
    refine ⟨23233371638256151414115897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15488914425504100942743931 23233371638256151414115897)
    ·
      refine ⟨17425028728692113560586923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23233371638256151414115897 17425028728692113560586923)
      ·
        refine ⟨26137543093038170340880385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17425028728692113560586923 26137543093038170340880385)
        ·
          refine ⟨19603157319778627755660289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26137543093038170340880385 19603157319778627755660289)
          ·
            refine ⟨14702367989833970816745217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19603157319778627755660289 14702367989833970816745217)
            ·
              refine ⟨11026775992375478112558913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14702367989833970816745217 11026775992375478112558913)
              ·
                refine ⟨8270081994281608584419185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11026775992375478112558913 8270081994281608584419185)
                ·
                  refine ⟨6202561495711206438314389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8270081994281608584419185 6202561495711206438314389)
                  ·
                    refine ⟨290745070111462801795987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6202561495711206438314389 290745070111462801795987)
                    ·
                      rfl

theorem cell22_849336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_849336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849336 prefixEnd_849336 := by exact prefixLift 849336
  have htrace : WordTrace (prefixWord ++ tailWord_849336) baseStart_849336 baseEnd_849336 := by
    simpa [prefixWord, tailWord_849336, baseEnd_849336] using wordTrace_append hprefix tailTrace_849336
  have hstable : (prefixWord ++ tailWord_849336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849336).length < 2 ^ (prefixWord ++ tailWord_849336).sum := by decide
  have hdescent : baseEnd_849336 < baseStart_849336 := by decide
  rcases family_descends (prefixWord ++ tailWord_849336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849351 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 9]
def baseStart_849351 : Nat := 118140960795 + 849351 * 2 ^ 59
def prefixEnd_849351 : Nat := 4983230072969 + 3 ^ 40 * 849351 * 2
def baseEnd_849351 : Nat := 96916734972669254223647

theorem tailTrace_849351 : CollatzResearch.WordTrace tailWord_849351 prefixEnd_849351 96916734972669254223647 := by
  unfold tailWord_849351
  simp only [CollatzResearch.WordTrace]
  refine ⟨30978375945953859447283907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20652250630635906298189271 30978375945953859447283907)
  ·
    refine ⟨46467563918930789170925861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30978375945953859447283907 46467563918930789170925861)
    ·
      refine ⟨8712668234799522969548599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46467563918930789170925861 8712668234799522969548599)
      ·
        refine ⟨13069002352199284454322899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8712668234799522969548599 13069002352199284454322899)
        ·
          refine ⟨19603503528298926681484349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13069002352199284454322899 19603503528298926681484349)
          ·
            refine ⟨7351313823112097505556631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19603503528298926681484349 7351313823112097505556631)
            ·
              refine ⟨11026970734668146258334947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7351313823112097505556631 11026970734668146258334947)
              ·
                refine ⟨16540456102002219387502421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11026970734668146258334947 16540456102002219387502421)
                ·
                  refine ⟨96916734972669254223647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16540456102002219387502421 96916734972669254223647)
                  ·
                    rfl

theorem cell22_849351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 9].length) (baseStart_849351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849351 prefixEnd_849351 := by exact prefixLift 849351
  have htrace : WordTrace (prefixWord ++ tailWord_849351) baseStart_849351 baseEnd_849351 := by
    simpa [prefixWord, tailWord_849351, baseEnd_849351] using wordTrace_append hprefix tailTrace_849351
  have hstable : (prefixWord ++ tailWord_849351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849351).length < 2 ^ (prefixWord ++ tailWord_849351).sum := by decide
  have hdescent : baseEnd_849351 < baseStart_849351 := by decide
  rcases family_descends (prefixWord ++ tailWord_849351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849479 : List Nat := [1, 1, 4, 1, 5, 2, 1, 2, 2, 3]
def baseStart_849479 : Nat := 118140960795 + 849479 * 2 ^ 59
def prefixEnd_849479 : Nat := 4983230072969 + 3 ^ 40 * 849479 * 2
def baseEnd_849479 : Nat := 290794021933858095470549

theorem tailTrace_849479 : CollatzResearch.WordTrace tailWord_849479 prefixEnd_849479 290794021933858095470549 := by
  unfold tailWord_849479
  simp only [CollatzResearch.WordTrace]
  refine ⟨30983044489490137307943491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20655362992993424871962327 30983044489490137307943491)
  ·
    refine ⟨46474566734235205961915237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30983044489490137307943491 46474566734235205961915237)
    ·
      refine ⟨8713981262669101117859107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46474566734235205961915237 8713981262669101117859107)
      ·
        refine ⟨13070971894003651676788661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8713981262669101117859107 13070971894003651676788661)
        ·
          refine ⟨1225403615062842344698937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13070971894003651676788661 1225403615062842344698937)
          ·
            refine ⟨919052711297131758524203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1225403615062842344698937 919052711297131758524203)
            ·
              refine ⟨1378579066945697637786305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 919052711297131758524203 1378579066945697637786305)
              ·
                refine ⟨1033934300209273228339729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1378579066945697637786305 1033934300209273228339729)
                ·
                  refine ⟨775450725156954921254797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1033934300209273228339729 775450725156954921254797)
                  ·
                    refine ⟨290794021933858095470549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 775450725156954921254797 290794021933858095470549)
                    ·
                      rfl

theorem cell22_849479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_849479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849479 prefixEnd_849479 := by exact prefixLift 849479
  have htrace : WordTrace (prefixWord ++ tailWord_849479) baseStart_849479 baseEnd_849479 := by
    simpa [prefixWord, tailWord_849479, baseEnd_849479] using wordTrace_append hprefix tailTrace_849479
  have hstable : (prefixWord ++ tailWord_849479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849479).length < 2 ^ (prefixWord ++ tailWord_849479).sum := by decide
  have hdescent : baseEnd_849479 < baseStart_849479 := by decide
  rcases family_descends (prefixWord ++ tailWord_849479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849629 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 1, 6]
def baseStart_849629 : Nat := 118140960795 + 849629 * 2 ^ 59
def prefixEnd_849629 : Nat := 4983230072969 + 3 ^ 40 * 849629 * 2
def baseEnd_849629 : Nat := 290845369999307704220089

theorem tailTrace_849629 : CollatzResearch.WordTrace tailWord_849629 prefixEnd_849629 290845369999307704220089 := by
  unfold tailWord_849629
  simp only [CollatzResearch.WordTrace]
  refine ⟨30988515438946712925903941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20659010292631141950602627 30988515438946712925903941)
  ·
    refine ⟨5810346644802508673606989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30988515438946712925903941 5810346644802508673606989)
    ·
      refine ⟨2178879991800940752602621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5810346644802508673606989 2178879991800940752602621)
      ·
        refine ⟨817079996925352782225983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2178879991800940752602621 817079996925352782225983)
        ·
          refine ⟨1225619995388029173338975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817079996925352782225983 1225619995388029173338975)
          ·
            refine ⟨1838429993082043760008463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225619995388029173338975 1838429993082043760008463)
            ·
              refine ⟨2757644989623065640012695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1838429993082043760008463 2757644989623065640012695)
              ·
                refine ⟨4136467484434598460019043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2757644989623065640012695 4136467484434598460019043)
                ·
                  refine ⟨6204701226651897690028565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4136467484434598460019043 6204701226651897690028565)
                  ·
                    refine ⟨290845369999307704220089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6204701226651897690028565 290845369999307704220089)
                    ·
                      rfl

theorem cell22_849629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_849629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849629 prefixEnd_849629 := by exact prefixLift 849629
  have htrace : WordTrace (prefixWord ++ tailWord_849629) baseStart_849629 baseEnd_849629 := by
    simpa [prefixWord, tailWord_849629, baseEnd_849629] using wordTrace_append hprefix tailTrace_849629
  have hstable : (prefixWord ++ tailWord_849629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849629).length < 2 ^ (prefixWord ++ tailWord_849629).sum := by decide
  have hdescent : baseEnd_849629 < baseStart_849629 := by decide
  rcases family_descends (prefixWord ++ tailWord_849629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849710 : List Nat := [4, 1, 3, 2, 2, 1, 3, 2, 1, 3]
def baseStart_849710 : Nat := 118140960795 + 849710 * 2 ^ 59
def prefixEnd_849710 : Nat := 4983230072969 + 3 ^ 40 * 849710 * 2
def baseEnd_849710 : Nat := 290873097954650492944841

theorem tailTrace_849710 : CollatzResearch.WordTrace tailWord_849710 prefixEnd_849710 290873097954650492944841 := by
  unfold tailWord_849710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3873933718956657969950323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20660979834435509173068389 3873933718956657969950323)
  ·
    refine ⟨5810900578434986954925485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3873933718956657969950323 5810900578434986954925485)
    ·
      refine ⟨2179087716913120108097057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5810900578434986954925485 2179087716913120108097057)
      ·
        refine ⟨1634315787684840081072793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2179087716913120108097057 1634315787684840081072793)
        ·
          refine ⟨1225736840763630060804595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1634315787684840081072793 1225736840763630060804595)
          ·
            refine ⟨1838605261145445091206893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225736840763630060804595 1838605261145445091206893)
            ·
              refine ⟨689476972929541909202585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1838605261145445091206893 689476972929541909202585)
              ·
                refine ⟨517107729697156431901939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689476972929541909202585 517107729697156431901939)
                ·
                  refine ⟨775661594545734647852909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 517107729697156431901939 775661594545734647852909)
                  ·
                    refine ⟨290873097954650492944841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 775661594545734647852909 290873097954650492944841)
                    ·
                      rfl

theorem cell22_849710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_849710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849710 prefixEnd_849710 := by exact prefixLift 849710
  have htrace : WordTrace (prefixWord ++ tailWord_849710) baseStart_849710 baseEnd_849710 := by
    simpa [prefixWord, tailWord_849710, baseEnd_849710] using wordTrace_append hprefix tailTrace_849710
  have hstable : (prefixWord ++ tailWord_849710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849710).length < 2 ^ (prefixWord ++ tailWord_849710).sum := by decide
  have hdescent : baseEnd_849710 < baseStart_849710 := by decide
  rcases family_descends (prefixWord ++ tailWord_849710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849762 : List Nat := [3, 3, 2, 1, 2, 11]
def baseStart_849762 : Nat := 118140960795 + 849762 * 2 ^ 59
def prefixEnd_849762 : Nat := 4983230072969 + 3 ^ 40 * 849762 * 2
def baseEnd_849762 : Nat := 3591245661942465316601

theorem tailTrace_849762 : CollatzResearch.WordTrace tailWord_849762 prefixEnd_849762 3591245661942465316601 := by
  unfold tailWord_849762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7748341586866219160123885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20662244231643251093663693 7748341586866219160123885)
  ·
    refine ⟨2905628095074832185046457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7748341586866219160123885 2905628095074832185046457)
    ·
      refine ⟨2179221071306124138784843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2905628095074832185046457 2179221071306124138784843)
      ·
        refine ⟨3268831606959186208177265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2179221071306124138784843 3268831606959186208177265)
        ·
          refine ⟨2451623705219389656132949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3268831606959186208177265 2451623705219389656132949)
          ·
            refine ⟨3591245661942465316601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2451623705219389656132949 3591245661942465316601)
            ·
              rfl

theorem cell22_849762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 11].length) (baseStart_849762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849762 prefixEnd_849762 := by exact prefixLift 849762
  have htrace : WordTrace (prefixWord ++ tailWord_849762) baseStart_849762 baseEnd_849762 := by
    simpa [prefixWord, tailWord_849762, baseEnd_849762] using wordTrace_append hprefix tailTrace_849762
  have hstable : (prefixWord ++ tailWord_849762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849762).length < 2 ^ (prefixWord ++ tailWord_849762).sum := by decide
  have hdescent : baseEnd_849762 < baseStart_849762 := by decide
  rcases family_descends (prefixWord ++ tailWord_849762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849841 : List Nat := [1, 2, 2, 4, 2, 2, 3, 1, 5]
def baseStart_849841 : Nat := 118140960795 + 849841 * 2 ^ 59
def prefixEnd_849841 : Nat := 4983230072969 + 3 ^ 40 * 849841 * 2
def baseEnd_849841 : Nat := 96972647310603272639813

theorem tailTrace_849841 : CollatzResearch.WordTrace tailWord_849841 prefixEnd_849841 96972647310603272639813 := by
  unfold tailWord_849841
  simp only [CollatzResearch.WordTrace]
  refine ⟨30996247714178673132621377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20664165142785782088414251 30996247714178673132621377)
  ·
    refine ⟨23247185785634004849466033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30996247714178673132621377 23247185785634004849466033)
    ·
      refine ⟨17435389339225503637099525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23247185785634004849466033 17435389339225503637099525)
      ·
        refine ⟨3269135501104781931956161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17435389339225503637099525 3269135501104781931956161)
        ·
          refine ⟨2451851625828586448967121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3269135501104781931956161 2451851625828586448967121)
          ·
            refine ⟨1838888719371439836725341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2451851625828586448967121 1838888719371439836725341)
            ·
              refine ⟨689583269764289938772003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1838888719371439836725341 689583269764289938772003)
              ·
                refine ⟨1034374904646434908158005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689583269764289938772003 1034374904646434908158005)
                ·
                  refine ⟨96972647310603272639813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1034374904646434908158005 96972647310603272639813)
                  ·
                    rfl

theorem cell22_849841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 5].length) (baseStart_849841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849841 prefixEnd_849841 := by exact prefixLift 849841
  have htrace : WordTrace (prefixWord ++ tailWord_849841) baseStart_849841 baseEnd_849841 := by
    simpa [prefixWord, tailWord_849841, baseEnd_849841] using wordTrace_append hprefix tailTrace_849841
  have hstable : (prefixWord ++ tailWord_849841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849841).length < 2 ^ (prefixWord ++ tailWord_849841).sum := by decide
  have hdescent : baseEnd_849841 < baseStart_849841 := by decide
  rcases family_descends (prefixWord ++ tailWord_849841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849867 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 3, 5]
def baseStart_849867 : Nat := 118140960795 + 849867 * 2 ^ 59
def prefixEnd_849867 : Nat := 4983230072969 + 3 ^ 40 * 849867 * 2
def baseEnd_849867 : Nat := 290926842263154416769359

theorem tailTrace_849867 : CollatzResearch.WordTrace tailWord_849867 prefixEnd_849867 290926842263154416769359 := by
  unfold tailWord_849867
  simp only [CollatzResearch.WordTrace]
  refine ⟨30997196012084479573067855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20664797341389653048711903 30997196012084479573067855)
  ·
    refine ⟨46495794018126719359601783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30997196012084479573067855 46495794018126719359601783)
    ·
      refine ⟨69743691027190079039402675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46495794018126719359601783 69743691027190079039402675)
      ·
        refine ⟨104615536540785118559104013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69743691027190079039402675 104615536540785118559104013)
        ·
          refine ⟨39230826202794419459664005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104615536540785118559104013 39230826202794419459664005)
          ·
            refine ⟨7355779913023953648687001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39230826202794419459664005 7355779913023953648687001)
            ·
              refine ⟨5516834934767965236515251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7355779913023953648687001 5516834934767965236515251)
              ·
                refine ⟨8275252402151947854772877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5516834934767965236515251 8275252402151947854772877)
                ·
                  refine ⟨3103219650806980445539829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8275252402151947854772877 3103219650806980445539829)
                  ·
                    refine ⟨290926842263154416769359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3103219650806980445539829 290926842263154416769359)
                    ·
                      rfl

theorem cell22_849867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 5].length) (baseStart_849867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849867 prefixEnd_849867 := by exact prefixLift 849867
  have htrace : WordTrace (prefixWord ++ tailWord_849867) baseStart_849867 baseEnd_849867 := by
    simpa [prefixWord, tailWord_849867, baseEnd_849867] using wordTrace_append hprefix tailTrace_849867
  have hstable : (prefixWord ++ tailWord_849867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849867).length < 2 ^ (prefixWord ++ tailWord_849867).sum := by decide
  have hdescent : baseEnd_849867 < baseStart_849867 := by decide
  rcases family_descends (prefixWord ++ tailWord_849867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849912 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 2, 7]
def baseStart_849912 : Nat := 118140960795 + 849912 * 2 ^ 59
def prefixEnd_849912 : Nat := 4983230072969 + 3 ^ 40 * 849912 * 2
def baseEnd_849912 : Nat := 290942246682789299394221

theorem tailTrace_849912 : CollatzResearch.WordTrace tailWord_849912 prefixEnd_849912 290942246682789299394221 := by
  unfold tailWord_849912
  simp only [CollatzResearch.WordTrace]
  refine ⟨15499418648460726129227995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20665891531280968172303993 15499418648460726129227995)
  ·
    refine ⟨23249127972691089193841993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15499418648460726129227995 23249127972691089193841993)
    ·
      refine ⟨17436845979518316895381495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23249127972691089193841993 17436845979518316895381495)
      ·
        refine ⟨26155268969277475343072243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17436845979518316895381495 26155268969277475343072243)
        ·
          refine ⟨39232903453916213014608365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26155268969277475343072243 39232903453916213014608365)
          ·
            refine ⟨14712338795218579880478137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39232903453916213014608365 14712338795218579880478137)
            ·
              refine ⟨11034254096413934910358603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14712338795218579880478137 11034254096413934910358603)
              ·
                refine ⟨16551381144620902365537905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11034254096413934910358603 16551381144620902365537905)
                ·
                  refine ⟨12413535858465676774153429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16551381144620902365537905 12413535858465676774153429)
                  ·
                    refine ⟨290942246682789299394221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12413535858465676774153429 290942246682789299394221)
                    ·
                      rfl

theorem cell22_849912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_849912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_849912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_849912 prefixEnd_849912 := by exact prefixLift 849912
  have htrace : WordTrace (prefixWord ++ tailWord_849912) baseStart_849912 baseEnd_849912 := by
    simpa [prefixWord, tailWord_849912, baseEnd_849912] using wordTrace_append hprefix tailTrace_849912
  have hstable : (prefixWord ++ tailWord_849912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849912).length < 2 ^ (prefixWord ++ tailWord_849912).sum := by decide
  have hdescent : baseEnd_849912 < baseStart_849912 := by decide
  rcases family_descends (prefixWord ++ tailWord_849912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850051 : List Nat := [1, 1, 1, 3, 3, 4, 1, 2, 2, 4]
def baseStart_850051 : Nat := 118140960795 + 850051 * 2 ^ 59
def prefixEnd_850051 : Nat := 4983230072969 + 3 ^ 40 * 850051 * 2
def baseEnd_850051 : Nat := 290989829223439270168795

theorem tailTrace_850051 : CollatzResearch.WordTrace tailWord_850051 prefixEnd_850051 290989829223439270168795 := by
  unfold tailWord_850051
  simp only [CollatzResearch.WordTrace]
  refine ⟨31003907043417878997766007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20669271362278585998510671 31003907043417878997766007)
  ·
    refine ⟨46505860565126818496649011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31003907043417878997766007 46505860565126818496649011)
    ·
      refine ⟨69758790847690227744973517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46505860565126818496649011 69758790847690227744973517)
      ·
        refine ⟨26159546567883835404365069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69758790847690227744973517 26159546567883835404365069)
        ·
          refine ⟨9809829962956438276636901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26159546567883835404365069 9809829962956438276636901)
          ·
            refine ⟨1839343118054332176869419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9809829962956438276636901 1839343118054332176869419)
            ·
              refine ⟨2759014677081498265304129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1839343118054332176869419 2759014677081498265304129)
              ·
                refine ⟨2069261007811123698978097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2759014677081498265304129 2069261007811123698978097)
                ·
                  refine ⟨1551945755858342774233573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2069261007811123698978097 1551945755858342774233573)
                  ·
                    refine ⟨290989829223439270168795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1551945755858342774233573 290989829223439270168795)
                    ·
                      rfl

theorem cell22_850051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 4].length) (baseStart_850051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850051 prefixEnd_850051 := by exact prefixLift 850051
  have htrace : WordTrace (prefixWord ++ tailWord_850051) baseStart_850051 baseEnd_850051 := by
    simpa [prefixWord, tailWord_850051, baseEnd_850051] using wordTrace_append hprefix tailTrace_850051
  have hstable : (prefixWord ++ tailWord_850051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850051).length < 2 ^ (prefixWord ++ tailWord_850051).sum := by decide
  have hdescent : baseEnd_850051 < baseStart_850051 := by decide
  rcases family_descends (prefixWord ++ tailWord_850051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850066 : List Nat := [3, 2, 3, 1, 1, 1, 4, 7]
def baseStart_850066 : Nat := 118140960795 + 850066 * 2 ^ 59
def prefixEnd_850066 : Nat := 4983230072969 + 3 ^ 40 * 850066 * 2
def baseEnd_850066 : Nat := 32332773781109359004861

theorem tailTrace_850066 : CollatzResearch.WordTrace tailWord_850066 prefixEnd_850066 32332773781109359004861 := by
  unfold tailWord_850066
  simp only [CollatzResearch.WordTrace]
  refine ⟨7751113534590884139890513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20669636092242357706374701 7751113534590884139890513)
  ·
    refine ⟨5813335150943163104917885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7751113534590884139890513 5813335150943163104917885)
    ·
      refine ⟨2180000681603686164344207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5813335150943163104917885 2180000681603686164344207)
      ·
        refine ⟨3270001022405529246516311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2180000681603686164344207 3270001022405529246516311)
        ·
          refine ⟨4905001533608293869774467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3270001022405529246516311 4905001533608293869774467)
          ·
            refine ⟨7357502300412440804661701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4905001533608293869774467 7357502300412440804661701)
            ·
              refine ⟨1379531681327332650874069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7357502300412440804661701 1379531681327332650874069)
              ·
                refine ⟨32332773781109359004861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1379531681327332650874069 32332773781109359004861)
                ·
                  rfl

theorem cell22_850066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 7].length) (baseStart_850066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850066 prefixEnd_850066 := by exact prefixLift 850066
  have htrace : WordTrace (prefixWord ++ tailWord_850066) baseStart_850066 baseEnd_850066 := by
    simpa [prefixWord, tailWord_850066, baseEnd_850066] using wordTrace_append hprefix tailTrace_850066
  have hstable : (prefixWord ++ tailWord_850066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850066).length < 2 ^ (prefixWord ++ tailWord_850066).sum := by decide
  have hdescent : baseEnd_850066 < baseStart_850066 := by decide
  rcases family_descends (prefixWord ++ tailWord_850066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850100 : List Nat := [2, 5, 3, 1, 1, 10]
def baseStart_850100 : Nat := 118140960795 + 850100 * 2 ^ 59
def prefixEnd_850100 : Nat := 4983230072969 + 3 ^ 40 * 850100 * 2
def baseEnd_850100 : Nat := 3592674110182956490045

theorem tailTrace_850100 : CollatzResearch.WordTrace tailWord_850100 prefixEnd_850100 3592674110182956490045 := by
  unfold tailWord_850100
  simp only [CollatzResearch.WordTrace]
  refine ⟨15502847110120180183149877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20670462813493573577533169 15502847110120180183149877)
  ·
    refine ⟨1453391916573766892170301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15502847110120180183149877 1453391916573766892170301)
    ·
      refine ⟨545021968715162584563863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1453391916573766892170301 545021968715162584563863)
      ·
        refine ⟨817532953072743876845795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545021968715162584563863 817532953072743876845795)
        ·
          refine ⟨1226299429609115815268693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817532953072743876845795 1226299429609115815268693)
          ·
            refine ⟨3592674110182956490045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1226299429609115815268693 3592674110182956490045)
            ·
              rfl

theorem cell22_850100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 10].length) (baseStart_850100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850100 prefixEnd_850100 := by exact prefixLift 850100
  have htrace : WordTrace (prefixWord ++ tailWord_850100) baseStart_850100 baseEnd_850100 := by
    simpa [prefixWord, tailWord_850100, baseEnd_850100] using wordTrace_append hprefix tailTrace_850100
  have hstable : (prefixWord ++ tailWord_850100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850100).length < 2 ^ (prefixWord ++ tailWord_850100).sum := by decide
  have hdescent : baseEnd_850100 < baseStart_850100 := by decide
  rcases family_descends (prefixWord ++ tailWord_850100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850126 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_850126 : Nat := 118140960795 + 850126 * 2 ^ 59
def prefixEnd_850126 : Nat := 4983230072969 + 3 ^ 40 * 850126 * 2
def baseEnd_850126 : Nat := 291015503256164074543565

theorem tailTrace_850126 : CollatzResearch.WordTrace tailWord_850126 prefixEnd_850126 291015503256164074543565 := by
  unfold tailWord_850126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3875830314768270850843279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20671095012097444537830821 3875830314768270850843279)
  ·
    refine ⟨5813745472152406276264919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3875830314768270850843279 5813745472152406276264919)
    ·
      refine ⟨8720618208228609414397379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5813745472152406276264919 8720618208228609414397379)
      ·
        refine ⟨13080927312342914121596069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8720618208228609414397379 13080927312342914121596069)
        ·
          refine ⟨2452673871064296397799263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13080927312342914121596069 2452673871064296397799263)
          ·
            refine ⟨3679010806596444596698895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2452673871064296397799263 3679010806596444596698895)
            ·
              refine ⟨5518516209894666895048343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3679010806596444596698895 5518516209894666895048343)
              ·
                refine ⟨8277774314842000342572515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5518516209894666895048343 8277774314842000342572515)
                ·
                  refine ⟨12416661472263000513858773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8277774314842000342572515 12416661472263000513858773)
                  ·
                    refine ⟨291015503256164074543565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12416661472263000513858773 291015503256164074543565)
                    ·
                      rfl

theorem cell22_850126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_850126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850126 prefixEnd_850126 := by exact prefixLift 850126
  have htrace : WordTrace (prefixWord ++ tailWord_850126) baseStart_850126 baseEnd_850126 := by
    simpa [prefixWord, tailWord_850126, baseEnd_850126] using wordTrace_append hprefix tailTrace_850126
  have hstable : (prefixWord ++ tailWord_850126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850126).length < 2 ^ (prefixWord ++ tailWord_850126).sum := by decide
  have hdescent : baseEnd_850126 < baseStart_850126 := by decide
  rcases family_descends (prefixWord ++ tailWord_850126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850139 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 8]
def baseStart_850139 : Nat := 118140960795 + 850139 * 2 ^ 59
def prefixEnd_850139 : Nat := 4983230072969 + 3 ^ 40 * 850139 * 2
def baseEnd_850139 : Nat := 97006651140612124656175

theorem tailTrace_850139 : CollatzResearch.WordTrace tailWord_850139 prefixEnd_850139 97006651140612124656175 := by
  unfold tailWord_850139
  simp only [CollatzResearch.WordTrace]
  refine ⟨31007116667099070026969471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20671411111399380017979647 31007116667099070026969471)
  ·
    refine ⟨46510675000648605040454207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31007116667099070026969471 46510675000648605040454207)
    ·
      refine ⟨69766012500972907560681311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46510675000648605040454207 69766012500972907560681311)
      ·
        refine ⟨104649018751459361341021967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69766012500972907560681311 104649018751459361341021967)
        ·
          refine ⟨156973528127189042011532951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104649018751459361341021967 156973528127189042011532951)
          ·
            refine ⟨235460292190783563017299427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156973528127189042011532951 235460292190783563017299427)
            ·
              refine ⟨353190438286175344525949141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235460292190783563017299427 353190438286175344525949141)
              ·
                refine ⟨8277900897332234637326933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 353190438286175344525949141 8277900897332234637326933)
                ·
                  refine ⟨97006651140612124656175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8277900897332234637326933 97006651140612124656175)
                  ·
                    rfl

theorem cell22_850139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 8].length) (baseStart_850139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850139 prefixEnd_850139 := by exact prefixLift 850139
  have htrace : WordTrace (prefixWord ++ tailWord_850139) baseStart_850139 baseEnd_850139 := by
    simpa [prefixWord, tailWord_850139, baseEnd_850139] using wordTrace_append hprefix tailTrace_850139
  have hstable : (prefixWord ++ tailWord_850139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850139).length < 2 ^ (prefixWord ++ tailWord_850139).sum := by decide
  have hdescent : baseEnd_850139 < baseStart_850139 := by decide
  rcases family_descends (prefixWord ++ tailWord_850139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850186 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 1, 6]
def baseStart_850186 : Nat := 118140960795 + 850186 * 2 ^ 59
def prefixEnd_850186 : Nat := 4983230072969 + 3 ^ 40 * 850186 * 2
def baseEnd_850186 : Nat := 291036042482343918043381

theorem tailTrace_850186 : CollatzResearch.WordTrace tailWord_850186 prefixEnd_850186 291036042482343918043381 := by
  unfold tailWord_850186
  simp only [CollatzResearch.WordTrace]
  refine ⟨7752207724482199263482603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20672553931952531369286941 7752207724482199263482603)
  ·
    refine ⟨11628311586723298895223905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7752207724482199263482603 11628311586723298895223905)
    ·
      refine ⟨8721233690042474171417929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11628311586723298895223905 8721233690042474171417929)
      ·
        refine ⟨6540925267531855628563447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8721233690042474171417929 6540925267531855628563447)
        ·
          refine ⟨9811387901297783442845171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6540925267531855628563447 9811387901297783442845171)
          ·
            refine ⟨14717081851946675164267757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9811387901297783442845171 14717081851946675164267757)
            ·
              refine ⟨5518905694480003186600409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14717081851946675164267757 5518905694480003186600409)
              ·
                refine ⟨4139179270860002389950307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5518905694480003186600409 4139179270860002389950307)
                ·
                  refine ⟨6208768906290003584925461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4139179270860002389950307 6208768906290003584925461)
                  ·
                    refine ⟨291036042482343918043381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6208768906290003584925461 291036042482343918043381)
                    ·
                      rfl

theorem cell22_850186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_850186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850186 prefixEnd_850186 := by exact prefixLift 850186
  have htrace : WordTrace (prefixWord ++ tailWord_850186) baseStart_850186 baseEnd_850186 := by
    simpa [prefixWord, tailWord_850186, baseEnd_850186] using wordTrace_append hprefix tailTrace_850186
  have hstable : (prefixWord ++ tailWord_850186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850186).length < 2 ^ (prefixWord ++ tailWord_850186).sum := by decide
  have hdescent : baseEnd_850186 < baseStart_850186 := by decide
  rcases family_descends (prefixWord ++ tailWord_850186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850280 : List Nat := [2, 1, 4, 2, 2, 2, 2, 2, 5]
def baseStart_850280 : Nat := 118140960795 + 850280 * 2 ^ 59
def prefixEnd_850280 : Nat := 4983230072969 + 3 ^ 40 * 850280 * 2
def baseEnd_850280 : Nat := 97022740201119668731031

theorem tailTrace_850280 : CollatzResearch.WordTrace tailWord_850280 prefixEnd_850280 97022740201119668731031 := by
  unfold tailWord_850280
  simp only [CollatzResearch.WordTrace]
  refine ⟨15506129679794125553926147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20674839573058834071901529 15506129679794125553926147)
  ·
    refine ⟨23259194519691188330889221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15506129679794125553926147 23259194519691188330889221)
    ·
      refine ⟨4361098972442097812041729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23259194519691188330889221 4361098972442097812041729)
      ·
        refine ⟨3270824229331573359031297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4361098972442097812041729 3270824229331573359031297)
        ·
          refine ⟨2453118171998680019273473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3270824229331573359031297 2453118171998680019273473)
          ·
            refine ⟨1839838628999010014455105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2453118171998680019273473 1839838628999010014455105)
            ·
              refine ⟨1379878971749257510841329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1839838628999010014455105 1379878971749257510841329)
              ·
                refine ⟨1034909228811943133130997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1379878971749257510841329 1034909228811943133130997)
                ·
                  refine ⟨97022740201119668731031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1034909228811943133130997 97022740201119668731031)
                  ·
                    rfl

theorem cell22_850280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 5].length) (baseStart_850280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850280 prefixEnd_850280 := by exact prefixLift 850280
  have htrace : WordTrace (prefixWord ++ tailWord_850280) baseStart_850280 baseEnd_850280 := by
    simpa [prefixWord, tailWord_850280, baseEnd_850280] using wordTrace_append hprefix tailTrace_850280
  have hstable : (prefixWord ++ tailWord_850280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850280).length < 2 ^ (prefixWord ++ tailWord_850280).sum := by decide
  have hdescent : baseEnd_850280 < baseStart_850280 := by decide
  rcases family_descends (prefixWord ++ tailWord_850280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850308 : List Nat := [2, 3, 2, 1, 1, 2, 3, 2, 6]
def baseStart_850308 : Nat := 118140960795 + 850308 * 2 ^ 59
def prefixEnd_850308 : Nat := 4983230072969 + 3 ^ 40 * 850308 * 2
def baseEnd_850308 : Nat := 97025935191858755497669

theorem tailTrace_850308 : CollatzResearch.WordTrace tailWord_850308 prefixEnd_850308 97025935191858755497669 := by
  unfold tailWord_850308
  simp only [CollatzResearch.WordTrace]
  refine ⟨15506640301743405944935789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20675520402324541259914385 15506640301743405944935789)
  ·
    refine ⟨5814990113153777229350921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15506640301743405944935789 5814990113153777229350921)
    ·
      refine ⟨4361242584865332922013191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5814990113153777229350921 4361242584865332922013191)
      ·
        refine ⟨6541863877297999383019787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4361242584865332922013191 6541863877297999383019787)
        ·
          refine ⟨9812795815946999074529681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6541863877297999383019787 9812795815946999074529681)
          ·
            refine ⟨7359596861960249305897261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9812795815946999074529681 7359596861960249305897261)
            ·
              refine ⟨2759848823235093489711473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7359596861960249305897261 2759848823235093489711473)
              ·
                refine ⟨2069886617426320117283605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2759848823235093489711473 2069886617426320117283605)
                ·
                  refine ⟨97025935191858755497669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2069886617426320117283605 97025935191858755497669)
                  ·
                    rfl

theorem cell22_850308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_850308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850308 prefixEnd_850308 := by exact prefixLift 850308
  have htrace : WordTrace (prefixWord ++ tailWord_850308) baseStart_850308 baseEnd_850308 := by
    simpa [prefixWord, tailWord_850308, baseEnd_850308] using wordTrace_append hprefix tailTrace_850308
  have hstable : (prefixWord ++ tailWord_850308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850308).length < 2 ^ (prefixWord ++ tailWord_850308).sum := by decide
  have hdescent : baseEnd_850308 < baseStart_850308 := by decide
  rcases family_descends (prefixWord ++ tailWord_850308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850357 : List Nat := [1, 3, 3, 2, 3, 2, 1, 1, 1, 5]
def baseStart_850357 : Nat := 118140960795 + 850357 * 2 ^ 59
def prefixEnd_850357 : Nat := 4983230072969 + 3 ^ 40 * 850357 * 2
def baseEnd_850357 : Nat := 291094579276956472017857

theorem tailTrace_850357 : CollatzResearch.WordTrace tailWord_850357 prefixEnd_850357 291094579276956472017857 := by
  unfold tailWord_850357
  simp only [CollatzResearch.WordTrace]
  refine ⟨31015067780309293258405325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20676711853539528838936883 31015067780309293258405325)
  ·
    refine ⟨11630650417615984971901997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31015067780309293258405325 11630650417615984971901997)
    ·
      refine ⟨4361493906605994364463249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11630650417615984971901997 4361493906605994364463249)
      ·
        refine ⟨3271120429954495773347437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4361493906605994364463249 3271120429954495773347437)
        ·
          refine ⟨1226670161232935915005289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3271120429954495773347437 1226670161232935915005289)
          ·
            refine ⟨920002620924701936253967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1226670161232935915005289 920002620924701936253967)
            ·
              refine ⟨1380003931387052904380951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920002620924701936253967 1380003931387052904380951)
              ·
                refine ⟨2070005897080579356571427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1380003931387052904380951 2070005897080579356571427)
                ·
                  refine ⟨3105008845620869034857141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2070005897080579356571427 3105008845620869034857141)
                  ·
                    refine ⟨291094579276956472017857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3105008845620869034857141 291094579276956472017857)
                    ·
                      rfl

theorem cell22_850357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_850357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850357 prefixEnd_850357 := by exact prefixLift 850357
  have htrace : WordTrace (prefixWord ++ tailWord_850357) baseStart_850357 baseEnd_850357 := by
    simpa [prefixWord, tailWord_850357, baseEnd_850357] using wordTrace_append hprefix tailTrace_850357
  have hstable : (prefixWord ++ tailWord_850357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850357).length < 2 ^ (prefixWord ++ tailWord_850357).sum := by decide
  have hdescent : baseEnd_850357 < baseStart_850357 := by decide
  rcases family_descends (prefixWord ++ tailWord_850357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850490 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 1, 6]
def baseStart_850490 : Nat := 118140960795 + 850490 * 2 ^ 59
def prefixEnd_850490 : Nat := 4983230072969 + 3 ^ 40 * 850490 * 2
def baseEnd_850490 : Nat := 291140107894988458442449

theorem tailTrace_850490 : CollatzResearch.WordTrace tailWord_850490 prefixEnd_850490 291140107894988458442449 := by
  unfold tailWord_850490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7754979672206864243249231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20679945792551637981997949 7754979672206864243249231)
  ·
    refine ⟨11632469508310296364873847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7754979672206864243249231 11632469508310296364873847)
    ·
      refine ⟨17448704262465444547310771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11632469508310296364873847 17448704262465444547310771)
      ·
        refine ⟨26173056393698166820966157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17448704262465444547310771 26173056393698166820966157)
        ·
          refine ⟨9814896147636812557862309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26173056393698166820966157 9814896147636812557862309)
          ·
            refine ⟨1840293027681902354599183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9814896147636812557862309 1840293027681902354599183)
            ·
              refine ⟨2760439541522853531898775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1840293027681902354599183 2760439541522853531898775)
              ·
                refine ⟨4140659312284280297848163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760439541522853531898775 4140659312284280297848163)
                ·
                  refine ⟨6210988968426420446772245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4140659312284280297848163 6210988968426420446772245)
                  ·
                    refine ⟨291140107894988458442449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6210988968426420446772245 291140107894988458442449)
                    ·
                      rfl

theorem cell22_850490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_850490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850490 prefixEnd_850490 := by exact prefixLift 850490
  have htrace : WordTrace (prefixWord ++ tailWord_850490) baseStart_850490 baseEnd_850490 := by
    simpa [prefixWord, tailWord_850490, baseEnd_850490] using wordTrace_append hprefix tailTrace_850490
  have hstable : (prefixWord ++ tailWord_850490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850490).length < 2 ^ (prefixWord ++ tailWord_850490).sum := by decide
  have hdescent : baseEnd_850490 < baseStart_850490 := by decide
  rcases family_descends (prefixWord ++ tailWord_850490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850509 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_850509 : Nat := 118140960795 + 850509 * 2 ^ 59
def prefixEnd_850509 : Nat := 4983230072969 + 3 ^ 40 * 850509 * 2
def baseEnd_850509 : Nat := 291146611983278742217391

theorem tailTrace_850509 : CollatzResearch.WordTrace tailWord_850509 prefixEnd_850509 291146611983278742217391 := by
  unfold tailWord_850509
  simp only [CollatzResearch.WordTrace]
  refine ⟨31020611675758623217938581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20680407783839082145292387 31020611675758623217938581)
  ·
    refine ⟨1454091172301185463340871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31020611675758623217938581 1454091172301185463340871)
    ·
      refine ⟨2181136758451778195011307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1454091172301185463340871 2181136758451778195011307)
      ·
        refine ⟨3271705137677667292516961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2181136758451778195011307 3271705137677667292516961)
        ·
          refine ⟨2453778853258250469387721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3271705137677667292516961 2453778853258250469387721)
          ·
            refine ⟨1840334139943687852040791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2453778853258250469387721 1840334139943687852040791)
            ·
              refine ⟨2760501209915531778061187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1840334139943687852040791 2760501209915531778061187)
              ·
                refine ⟨4140751814873297667091781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760501209915531778061187 4140751814873297667091781)
                ·
                  refine ⟨776390965288743312579709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4140751814873297667091781 776390965288743312579709)
                  ·
                    refine ⟨291146611983278742217391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 776390965288743312579709 291146611983278742217391)
                    ·
                      rfl

theorem cell22_850509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_850509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850509 prefixEnd_850509 := by exact prefixLift 850509
  have htrace : WordTrace (prefixWord ++ tailWord_850509) baseStart_850509 baseEnd_850509 := by
    simpa [prefixWord, tailWord_850509, baseEnd_850509] using wordTrace_append hprefix tailTrace_850509
  have hstable : (prefixWord ++ tailWord_850509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850509).length < 2 ^ (prefixWord ++ tailWord_850509).sum := by decide
  have hdescent : baseEnd_850509 < baseStart_850509 := by decide
  rcases family_descends (prefixWord ++ tailWord_850509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850659 : List Nat := [1, 1, 1, 7, 1, 1, 3, 1, 2, 4]
def baseStart_850659 : Nat := 118140960795 + 850659 * 2 ^ 59
def prefixEnd_850659 : Nat := 4983230072969 + 3 ^ 40 * 850659 * 2
def baseEnd_850659 : Nat := 291197960048728350966931

theorem tailTrace_850659 : CollatzResearch.WordTrace tailWord_850659 prefixEnd_850659 291197960048728350966931 := by
  unfold tailWord_850659
  simp only [CollatzResearch.WordTrace]
  refine ⟨31026082625215198835899031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20684055083476799223932687 31026082625215198835899031)
  ·
    refine ⟨46539123937822798253848547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31026082625215198835899031 46539123937822798253848547)
    ·
      refine ⟨69808685906734197380772821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46539123937822798253848547 69808685906734197380772821)
      ·
        refine ⟨1636141075939082751111863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 69808685906734197380772821 1636141075939082751111863)
        ·
          refine ⟨2454211613908624126667795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636141075939082751111863 2454211613908624126667795)
          ·
            refine ⟨3681317420862936190001693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2454211613908624126667795 3681317420862936190001693)
            ·
              refine ⟨1380494032823601071250635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3681317420862936190001693 1380494032823601071250635)
              ·
                refine ⟨2070741049235401606875953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1380494032823601071250635 2070741049235401606875953)
                ·
                  refine ⟨1553055786926551205156965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2070741049235401606875953 1553055786926551205156965)
                  ·
                    refine ⟨291197960048728350966931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1553055786926551205156965 291197960048728350966931)
                    ·
                      rfl

theorem cell22_850659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 4].length) (baseStart_850659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850659 prefixEnd_850659 := by exact prefixLift 850659
  have htrace : WordTrace (prefixWord ++ tailWord_850659) baseStart_850659 baseEnd_850659 := by
    simpa [prefixWord, tailWord_850659, baseEnd_850659] using wordTrace_append hprefix tailTrace_850659
  have hstable : (prefixWord ++ tailWord_850659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850659).length < 2 ^ (prefixWord ++ tailWord_850659).sum := by decide
  have hdescent : baseEnd_850659 < baseStart_850659 := by decide
  rcases family_descends (prefixWord ++ tailWord_850659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850672 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 5, 3]
def baseStart_850672 : Nat := 118140960795 + 850672 * 2 ^ 59
def prefixEnd_850672 : Nat := 4983230072969 + 3 ^ 40 * 850672 * 2
def baseEnd_850672 : Nat := 291202410214400650391891

theorem tailTrace_850672 : CollatzResearch.WordTrace tailWord_850672 prefixEnd_850672 291202410214400650391891 := by
  unfold tailWord_850672
  simp only [CollatzResearch.WordTrace]
  refine ⟨15513278387084051028061135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20684371182778734704081513 15513278387084051028061135)
  ·
    refine ⟨23269917580626076542091703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15513278387084051028061135 23269917580626076542091703)
    ·
      refine ⟨34904876370939114813137555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23269917580626076542091703 34904876370939114813137555)
      ·
        refine ⟨52357314556408672219706333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34904876370939114813137555 52357314556408672219706333)
        ·
          refine ⟨19633992958653252082389875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52357314556408672219706333 19633992958653252082389875)
          ·
            refine ⟨29450989437979878123584813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19633992958653252082389875 29450989437979878123584813)
            ·
              refine ⟨11044121039242454296344305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29450989437979878123584813 11044121039242454296344305)
              ·
                refine ⟨8283090779431840722258229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11044121039242454296344305 8283090779431840722258229)
                ·
                  refine ⟨776539760571735067711709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8283090779431840722258229 776539760571735067711709)
                  ·
                    refine ⟨291202410214400650391891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 776539760571735067711709 291202410214400650391891)
                    ·
                      rfl

theorem cell22_850672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 5, 3].length) (baseStart_850672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850672 prefixEnd_850672 := by exact prefixLift 850672
  have htrace : WordTrace (prefixWord ++ tailWord_850672) baseStart_850672 baseEnd_850672 := by
    simpa [prefixWord, tailWord_850672, baseEnd_850672] using wordTrace_append hprefix tailTrace_850672
  have hstable : (prefixWord ++ tailWord_850672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850672).length < 2 ^ (prefixWord ++ tailWord_850672).sum := by decide
  have hdescent : baseEnd_850672 < baseStart_850672 := by decide
  rcases family_descends (prefixWord ++ tailWord_850672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850740 : List Nat := [2, 5, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_850740 : Nat := 118140960795 + 850740 * 2 ^ 59
def prefixEnd_850740 : Nat := 4983230072969 + 3 ^ 40 * 850740 * 2
def baseEnd_850740 : Nat := 291225688004071139691683

theorem tailTrace_850740 : CollatzResearch.WordTrace tailWord_850740 prefixEnd_850740 291225688004071139691683 := by
  unfold tailWord_850740
  simp only [CollatzResearch.WordTrace]
  refine ⟨15514518468960874834798837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20686024625281166446398449 15514518468960874834798837)
  ·
    refine ⟨1454486106465082015762391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15514518468960874834798837 1454486106465082015762391)
    ·
      refine ⟨2181729159697623023643587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1454486106465082015762391 2181729159697623023643587)
      ·
        refine ⟨3272593739546434535465381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2181729159697623023643587 3272593739546434535465381)
        ·
          refine ⟨613611326164956475399759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3272593739546434535465381 613611326164956475399759)
          ·
            refine ⟨920416989247434713099639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613611326164956475399759 920416989247434713099639)
            ·
              refine ⟨1380625483871152069649459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920416989247434713099639 1380625483871152069649459)
              ·
                refine ⟨2070938225806728104474189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1380625483871152069649459 2070938225806728104474189)
                ·
                  refine ⟨776601834677523039177821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2070938225806728104474189 776601834677523039177821)
                  ·
                    refine ⟨291225688004071139691683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 776601834677523039177821 291225688004071139691683)
                    ·
                      rfl

theorem cell22_850740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_850740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850740 prefixEnd_850740 := by exact prefixLift 850740
  have htrace : WordTrace (prefixWord ++ tailWord_850740) baseStart_850740 baseEnd_850740 := by
    simpa [prefixWord, tailWord_850740, baseEnd_850740] using wordTrace_append hprefix tailTrace_850740
  have hstable : (prefixWord ++ tailWord_850740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850740).length < 2 ^ (prefixWord ++ tailWord_850740).sum := by decide
  have hdescent : baseEnd_850740 < baseStart_850740 := by decide
  rcases family_descends (prefixWord ++ tailWord_850740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850792 : List Nat := [2, 1, 4, 2, 1, 12]
def baseStart_850792 : Nat := 118140960795 + 850792 * 2 ^ 59
def prefixEnd_850792 : Nat := 4983230072969 + 3 ^ 40 * 850792 * 2
def baseEnd_850792 : Nat := 3595598625515559720883

theorem tailTrace_850792 : CollatzResearch.WordTrace tailWord_850792 prefixEnd_850792 3595598625515559720883 := by
  unfold tailWord_850792
  simp only [CollatzResearch.WordTrace]
  refine ⟨15515466766866681275245315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20687289022488908366993753 15515466766866681275245315)
  ·
    refine ⟨23273200150300021912867973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15515466766866681275245315 23273200150300021912867973)
    ·
      refine ⟨4363725028181254108662745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23273200150300021912867973 4363725028181254108662745)
      ·
        refine ⟨3272793771135940581497059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4363725028181254108662745 3272793771135940581497059)
        ·
          refine ⟨4909190656703910872245589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3272793771135940581497059 4909190656703910872245589)
          ·
            refine ⟨3595598625515559720883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4909190656703910872245589 3595598625515559720883)
            ·
              rfl

theorem cell22_850792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 12].length) (baseStart_850792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850792 prefixEnd_850792 := by exact prefixLift 850792
  have htrace : WordTrace (prefixWord ++ tailWord_850792) baseStart_850792 baseEnd_850792 := by
    simpa [prefixWord, tailWord_850792, baseEnd_850792] using wordTrace_append hprefix tailTrace_850792
  have hstable : (prefixWord ++ tailWord_850792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850792).length < 2 ^ (prefixWord ++ tailWord_850792).sum := by decide
  have hdescent : baseEnd_850792 < baseStart_850792 := by decide
  rcases family_descends (prefixWord ++ tailWord_850792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850796 : List Nat := [2, 2, 1, 1, 4, 1, 4, 2, 2, 3]
def baseStart_850796 : Nat := 118140960795 + 850796 * 2 ^ 59
def prefixEnd_850796 : Nat := 4983230072969 + 3 ^ 40 * 850796 * 2
def baseEnd_850796 : Nat := 291244857948505660291511

theorem tailTrace_850796 : CollatzResearch.WordTrace tailWord_850796 prefixEnd_850796 291244857948505660291511 := by
  unfold tailWord_850796
  simp only [CollatzResearch.WordTrace]
  refine ⟨15515539712859435616818121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20687386283812580822424161 15515539712859435616818121)
  ·
    refine ⟨11636654784644576712613591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15515539712859435616818121 11636654784644576712613591)
    ·
      refine ⟨17454982176966865068920387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11636654784644576712613591 17454982176966865068920387)
      ·
        refine ⟨26182473265450297603380581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17454982176966865068920387 26182473265450297603380581)
        ·
          refine ⟨4909213737271930800633859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26182473265450297603380581 4909213737271930800633859)
          ·
            refine ⟨7363820605907896200950789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4909213737271930800633859 7363820605907896200950789)
            ·
              refine ⟨1380716363607730537678273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7363820605907896200950789 1380716363607730537678273)
              ·
                refine ⟨1035537272705797903258705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1380716363607730537678273 1035537272705797903258705)
                ·
                  refine ⟨776652954529348427444029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1035537272705797903258705 776652954529348427444029)
                  ·
                    refine ⟨291244857948505660291511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 776652954529348427444029 291244857948505660291511)
                    ·
                      rfl

theorem cell22_850796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_850796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850796 prefixEnd_850796 := by exact prefixLift 850796
  have htrace : WordTrace (prefixWord ++ tailWord_850796) baseStart_850796 baseEnd_850796 := by
    simpa [prefixWord, tailWord_850796, baseEnd_850796] using wordTrace_append hprefix tailTrace_850796
  have hstable : (prefixWord ++ tailWord_850796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850796).length < 2 ^ (prefixWord ++ tailWord_850796).sum := by decide
  have hdescent : baseEnd_850796 < baseStart_850796 := by decide
  rcases family_descends (prefixWord ++ tailWord_850796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850798 : List Nat := [4, 1, 2, 3, 2, 1, 1, 4, 4]
def baseStart_850798 : Nat := 118140960795 + 850798 * 2 ^ 59
def prefixEnd_850798 : Nat := 4983230072969 + 3 ^ 40 * 850798 * 2
def baseEnd_850798 : Nat := 97081847529792773913835

theorem tailTrace_850798 : CollatzResearch.WordTrace tailWord_850798 prefixEnd_850798 97081847529792773913835 := by
  unfold tailWord_850798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3878894046463953196901131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20687434914474417050139365 3878894046463953196901131)
  ·
    refine ⟨5818341069695929795351697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3878894046463953196901131 5818341069695929795351697)
    ·
      refine ⟨4363755802271947346513773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5818341069695929795351697 4363755802271947346513773)
      ·
        refine ⟨1636408425851980254942665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4363755802271947346513773 1636408425851980254942665)
        ·
          refine ⟨1227306319388985191206999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1636408425851980254942665 1227306319388985191206999)
          ·
            refine ⟨1840959479083477786810499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227306319388985191206999 1840959479083477786810499)
            ·
              refine ⟨2761439218625216680215749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1840959479083477786810499 2761439218625216680215749)
              ·
                refine ⟨517769853492228127540453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2761439218625216680215749 517769853492228127540453)
                ·
                  refine ⟨97081847529792773913835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 517769853492228127540453 97081847529792773913835)
                  ·
                    rfl

theorem cell22_850798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_850798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850798 prefixEnd_850798 := by exact prefixLift 850798
  have htrace : WordTrace (prefixWord ++ tailWord_850798) baseStart_850798 baseEnd_850798 := by
    simpa [prefixWord, tailWord_850798, baseEnd_850798] using wordTrace_append hprefix tailTrace_850798
  have hstable : (prefixWord ++ tailWord_850798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850798).length < 2 ^ (prefixWord ++ tailWord_850798).sum := by decide
  have hdescent : baseEnd_850798 < baseStart_850798 := by decide
  rcases family_descends (prefixWord ++ tailWord_850798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850809 : List Nat := [1, 2, 1, 3, 2, 5, 1, 7]
def baseStart_850809 : Nat := 118140960795 + 850809 * 2 ^ 59
def prefixEnd_850809 : Nat := 4983230072969 + 3 ^ 40 * 850809 * 2
def baseEnd_850809 : Nat := 32361034234908662190719

theorem tailTrace_850809 : CollatzResearch.WordTrace tailWord_850809 prefixEnd_850809 32361034234908662190719 := by
  unfold tailWord_850809
  simp only [CollatzResearch.WordTrace]
  refine ⟨31031553574671774453859481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20687702383114516302572987 31031553574671774453859481)
  ·
    refine ⟨23273665181003830840394611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31031553574671774453859481 23273665181003830840394611)
    ·
      refine ⟨34910497771505746260591917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23273665181003830840394611 34910497771505746260591917)
      ·
        refine ⟨13091436664314654847721969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34910497771505746260591917 13091436664314654847721969)
        ·
          refine ⟨9818577498235991135791477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13091436664314654847721969 9818577498235991135791477)
          ·
            refine ⟨920491640459624168980451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9818577498235991135791477 920491640459624168980451)
            ·
              refine ⟨1380737460689436253470677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920491640459624168980451 1380737460689436253470677)
              ·
                refine ⟨32361034234908662190719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1380737460689436253470677 32361034234908662190719)
                ·
                  rfl

theorem cell22_850809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 7].length) (baseStart_850809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850809 prefixEnd_850809 := by exact prefixLift 850809
  have htrace : WordTrace (prefixWord ++ tailWord_850809) baseStart_850809 baseEnd_850809 := by
    simpa [prefixWord, tailWord_850809, baseEnd_850809] using wordTrace_append hprefix tailTrace_850809
  have hstable : (prefixWord ++ tailWord_850809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850809).length < 2 ^ (prefixWord ++ tailWord_850809).sum := by decide
  have hdescent : baseEnd_850809 < baseStart_850809 := by decide
  rcases family_descends (prefixWord ++ tailWord_850809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850826 : List Nat := [3, 1, 2, 4, 1, 2, 3, 6]
def baseStart_850826 : Nat := 118140960795 + 850826 * 2 ^ 59
def prefixEnd_850826 : Nat := 4983230072969 + 3 ^ 40 * 850826 * 2
def baseEnd_850826 : Nat := 32361680840177286893491

theorem tailTrace_850826 : CollatzResearch.WordTrace tailWord_850826 prefixEnd_850826 32361680840177286893491 := by
  unfold tailWord_850826
  simp only [CollatzResearch.WordTrace]
  refine ⟨7758043403902546589307083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20688115743740124238152221 7758043403902546589307083)
  ·
    refine ⟨11637065105853819883960625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7758043403902546589307083 11637065105853819883960625)
    ·
      refine ⟨8727798829390364912970469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11637065105853819883960625 8727798829390364912970469)
      ·
        refine ⟨1636462280510693421181963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8727798829390364912970469 1636462280510693421181963)
        ·
          refine ⟨2454693420766040131772945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636462280510693421181963 2454693420766040131772945)
          ·
            refine ⟨1841020065574530098829709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2454693420766040131772945 1841020065574530098829709)
            ·
              refine ⟨690382524590448787061141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1841020065574530098829709 690382524590448787061141)
              ·
                refine ⟨32361680840177286893491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 690382524590448787061141 32361680840177286893491)
                ·
                  rfl

theorem cell22_850826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 6].length) (baseStart_850826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850826 prefixEnd_850826 := by exact prefixLift 850826
  have htrace : WordTrace (prefixWord ++ tailWord_850826) baseStart_850826 baseEnd_850826 := by
    simpa [prefixWord, tailWord_850826, baseEnd_850826] using wordTrace_append hprefix tailTrace_850826
  have hstable : (prefixWord ++ tailWord_850826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850826).length < 2 ^ (prefixWord ++ tailWord_850826).sum := by decide
  have hdescent : baseEnd_850826 < baseStart_850826 := by decide
  rcases family_descends (prefixWord ++ tailWord_850826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850867 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 2, 8]
def baseStart_850867 : Nat := 118140960795 + 850867 * 2 ^ 59
def prefixEnd_850867 : Nat := 4983230072969 + 3 ^ 40 * 850867 * 2
def baseEnd_850867 : Nat := 291269162699485141766293

theorem tailTrace_850867 : CollatzResearch.WordTrace tailWord_850867 prefixEnd_850867 291269162699485141766293 := by
  unfold tailWord_850867
  simp only [CollatzResearch.WordTrace]
  refine ⟨31033669008461650359470855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20689112672307766906313903 31033669008461650359470855)
  ·
    refine ⟨46550503512692475539206283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31033669008461650359470855 46550503512692475539206283)
    ·
      refine ⟨69825755269038713308809425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46550503512692475539206283 69825755269038713308809425)
      ·
        refine ⟨52369316451779034981607069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69825755269038713308809425 52369316451779034981607069)
        ·
          refine ⟨19638493669417138118102651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52369316451779034981607069 19638493669417138118102651)
          ·
            refine ⟨29457740504125707177153977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19638493669417138118102651 29457740504125707177153977)
            ·
              refine ⟨22093305378094280382865483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29457740504125707177153977 22093305378094280382865483)
              ·
                refine ⟨33139958067141420574298225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22093305378094280382865483 33139958067141420574298225)
                ·
                  refine ⟨24854968550356065430723669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33139958067141420574298225 24854968550356065430723669)
                  ·
                    refine ⟨291269162699485141766293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24854968550356065430723669 291269162699485141766293)
                    ·
                      rfl

theorem cell22_850867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 8].length) (baseStart_850867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850867 prefixEnd_850867 := by exact prefixLift 850867
  have htrace : WordTrace (prefixWord ++ tailWord_850867) baseStart_850867 baseEnd_850867 := by
    simpa [prefixWord, tailWord_850867, baseEnd_850867] using wordTrace_append hprefix tailTrace_850867
  have hstable : (prefixWord ++ tailWord_850867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850867).length < 2 ^ (prefixWord ++ tailWord_850867).sum := by decide
  have hdescent : baseEnd_850867 < baseStart_850867 := by decide
  rcases family_descends (prefixWord ++ tailWord_850867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850869 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 2, 5]
def baseStart_850869 : Nat := 118140960795 + 850869 * 2 ^ 59
def prefixEnd_850869 : Nat := 4983230072969 + 3 ^ 40 * 850869 * 2
def baseEnd_850869 : Nat := 291269847340357803216287

theorem tailTrace_850869 : CollatzResearch.WordTrace tailWord_850869 prefixEnd_850869 291269847340357803216287 := by
  unfold tailWord_850869
  simp only [CollatzResearch.WordTrace]
  refine ⟨31033741954454404701043661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20689161302969603134029107 31033741954454404701043661)
  ·
    refine ⟨11637653232920401762891373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31033741954454404701043661 11637653232920401762891373)
    ·
      refine ⟨4364119962345150661084265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11637653232920401762891373 4364119962345150661084265)
      ·
        refine ⟨3273089971758862995813199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4364119962345150661084265 3273089971758862995813199)
        ·
          refine ⟨4909634957638294493719799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3273089971758862995813199 4909634957638294493719799)
          ·
            refine ⟨7364452436457441740579699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4909634957638294493719799 7364452436457441740579699)
            ·
              refine ⟨11046678654686162610869549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7364452436457441740579699 11046678654686162610869549)
              ·
                refine ⟨4142504495507310979076081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11046678654686162610869549 4142504495507310979076081)
                ·
                  refine ⟨3106878371630483234307061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4142504495507310979076081 3106878371630483234307061)
                  ·
                    refine ⟨291269847340357803216287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3106878371630483234307061 291269847340357803216287)
                    ·
                      rfl

theorem cell22_850869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_850869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_850869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_850869 prefixEnd_850869 := by exact prefixLift 850869
  have htrace : WordTrace (prefixWord ++ tailWord_850869) baseStart_850869 baseEnd_850869 := by
    simpa [prefixWord, tailWord_850869, baseEnd_850869] using wordTrace_append hprefix tailTrace_850869
  have hstable : (prefixWord ++ tailWord_850869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850869).length < 2 ^ (prefixWord ++ tailWord_850869).sum := by decide
  have hdescent : baseEnd_850869 < baseStart_850869 := by decide
  rcases family_descends (prefixWord ++ tailWord_850869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851053 : List Nat := [1, 5, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_851053 : Nat := 118140960795 + 851053 * 2 ^ 59
def prefixEnd_851053 : Nat := 4983230072969 + 3 ^ 40 * 851053 * 2
def baseEnd_851053 : Nat := 291332834300642656615723

theorem tailTrace_851053 : CollatzResearch.WordTrace tailWord_851053 prefixEnd_851053 291332834300642656615723 := by
  unfold tailWord_851053
  simp only [CollatzResearch.WordTrace]
  refine ⟨31040452985787804125741813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20693635323858536083827875 31040452985787804125741813)
  ·
    refine ⟨2910042467417606636788295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31040452985787804125741813 2910042467417606636788295)
    ·
      refine ⟨4365063701126409955182443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2910042467417606636788295 4365063701126409955182443)
      ·
        refine ⟨6547595551689614932773665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4365063701126409955182443 6547595551689614932773665)
        ·
          refine ⟨4910696663767211199580249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6547595551689614932773665 4910696663767211199580249)
          ·
            refine ⟨3683022497825408399685187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4910696663767211199580249 3683022497825408399685187)
            ·
              refine ⟨5524533746738112599527781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3683022497825408399685187 5524533746738112599527781)
              ·
                refine ⟨1035850077513396112411459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5524533746738112599527781 1035850077513396112411459)
                ·
                  refine ⟨1553775116270094168617189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1035850077513396112411459 1553775116270094168617189)
                  ·
                    refine ⟨291332834300642656615723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1553775116270094168617189 291332834300642656615723)
                    ·
                      rfl

theorem cell22_851053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_851053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851053 prefixEnd_851053 := by exact prefixLift 851053
  have htrace : WordTrace (prefixWord ++ tailWord_851053) baseStart_851053 baseEnd_851053 := by
    simpa [prefixWord, tailWord_851053, baseEnd_851053] using wordTrace_append hprefix tailTrace_851053
  have hstable : (prefixWord ++ tailWord_851053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851053).length < 2 ^ (prefixWord ++ tailWord_851053).sum := by decide
  have hdescent : baseEnd_851053 < baseStart_851053 := by decide
  rcases family_descends (prefixWord ++ tailWord_851053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851061 : List Nat := [1, 3, 4, 3, 2, 1, 1, 3, 1, 3]
def baseStart_851061 : Nat := 118140960795 + 851061 * 2 ^ 59
def prefixEnd_851061 : Nat := 4983230072969 + 3 ^ 40 * 851061 * 2
def baseEnd_851061 : Nat := 291335572864133302415699

theorem tailTrace_851061 : CollatzResearch.WordTrace tailWord_851061 prefixEnd_851061 291335572864133302415699 := by
  unfold tailWord_851061
  simp only [CollatzResearch.WordTrace]
  refine ⟨31040744769758821492033037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20693829846505880994688691 31040744769758821492033037)
  ·
    refine ⟨11640279288659558059512389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31040744769758821492033037 11640279288659558059512389)
    ·
      refine ⟨2182552366623667136158573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11640279288659558059512389 2182552366623667136158573)
      ·
        refine ⟨818457137483875176059465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2182552366623667136158573 818457137483875176059465)
        ·
          refine ⟨613842853112906382044599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 818457137483875176059465 613842853112906382044599)
          ·
            refine ⟨920764279669359573066899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613842853112906382044599 920764279669359573066899)
            ·
              refine ⟨1381146419504039359600349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920764279669359573066899 1381146419504039359600349)
              ·
                refine ⟨517929907314014759850131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1381146419504039359600349 517929907314014759850131)
                ·
                  refine ⟨776894860971022139775197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 517929907314014759850131 776894860971022139775197)
                  ·
                    refine ⟨291335572864133302415699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 776894860971022139775197 291335572864133302415699)
                    ·
                      rfl

theorem cell22_851061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_851061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851061 prefixEnd_851061 := by exact prefixLift 851061
  have htrace : WordTrace (prefixWord ++ tailWord_851061) baseStart_851061 baseEnd_851061 := by
    simpa [prefixWord, tailWord_851061, baseEnd_851061] using wordTrace_append hprefix tailTrace_851061
  have hstable : (prefixWord ++ tailWord_851061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851061).length < 2 ^ (prefixWord ++ tailWord_851061).sum := by decide
  have hdescent : baseEnd_851061 < baseStart_851061 := by decide
  rcases family_descends (prefixWord ++ tailWord_851061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851081 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 4, 4]
def baseStart_851081 : Nat := 118140960795 + 851081 * 2 ^ 59
def prefixEnd_851081 : Nat := 4983230072969 + 3 ^ 40 * 851081 * 2
def baseEnd_851081 : Nat := 291342419272859916915637

theorem tailTrace_851081 : CollatzResearch.WordTrace tailWord_851081 prefixEnd_851081 291342419272859916915637 := by
  unfold tailWord_851081
  simp only [CollatzResearch.WordTrace]
  refine ⟨31041474229686364907761097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20694316153124243271840731 31041474229686364907761097)
  ·
    refine ⟨23281105672264773680820823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31041474229686364907761097 23281105672264773680820823)
    ·
      refine ⟨34921658508397160521231235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23281105672264773680820823 34921658508397160521231235)
      ·
        refine ⟨52382487762595740781846853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34921658508397160521231235 52382487762595740781846853)
        ·
          refine ⟨9821716455486701396596285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52382487762595740781846853 9821716455486701396596285)
          ·
            refine ⟨3683143670807513023723607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9821716455486701396596285 3683143670807513023723607)
            ·
              refine ⟨5524715506211269535585411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3683143670807513023723607 5524715506211269535585411)
              ·
                refine ⟨8287073259316904303378117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5524715506211269535585411 8287073259316904303378117)
                ·
                  refine ⟨1553826236121919556883397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8287073259316904303378117 1553826236121919556883397)
                  ·
                    refine ⟨291342419272859916915637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1553826236121919556883397 291342419272859916915637)
                    ·
                      rfl

theorem cell22_851081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_851081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851081 prefixEnd_851081 := by exact prefixLift 851081
  have htrace : WordTrace (prefixWord ++ tailWord_851081) baseStart_851081 baseEnd_851081 := by
    simpa [prefixWord, tailWord_851081, baseEnd_851081] using wordTrace_append hprefix tailTrace_851081
  have hstable : (prefixWord ++ tailWord_851081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851081).length < 2 ^ (prefixWord ++ tailWord_851081).sum := by decide
  have hdescent : baseEnd_851081 < baseStart_851081 := by decide
  rcases family_descends (prefixWord ++ tailWord_851081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851096 : List Nat := [2, 1, 2, 4, 2, 1, 1, 9]
def baseStart_851096 : Nat := 118140960795 + 851096 * 2 ^ 59
def prefixEnd_851096 : Nat := 4983230072969 + 3 ^ 40 * 851096 * 2
def baseEnd_851096 : Nat := 32371950453267208643399

theorem tailTrace_851096 : CollatzResearch.WordTrace tailWord_851096 prefixEnd_851096 32371950453267208643399 := by
  unfold tailWord_851096
  simp only [CollatzResearch.WordTrace]
  refine ⟨15521010662316011234778571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20694680883088014979704761 15521010662316011234778571)
  ·
    refine ⟨23281515993474016852167857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15521010662316011234778571 23281515993474016852167857)
    ·
      refine ⟨17461136995105512639125893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23281515993474016852167857 17461136995105512639125893)
      ·
        refine ⟨3273963186582283619836105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17461136995105512639125893 3273963186582283619836105)
        ·
          refine ⟨2455472389936712714877079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3273963186582283619836105 2455472389936712714877079)
          ·
            refine ⟨3683208584905069072315619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2455472389936712714877079 3683208584905069072315619)
            ·
              refine ⟨5524812877357603608473429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3683208584905069072315619 5524812877357603608473429)
              ·
                refine ⟨32371950453267208643399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5524812877357603608473429 32371950453267208643399)
                ·
                  rfl

theorem cell22_851096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 9].length) (baseStart_851096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851096 prefixEnd_851096 := by exact prefixLift 851096
  have htrace : WordTrace (prefixWord ++ tailWord_851096) baseStart_851096 baseEnd_851096 := by
    simpa [prefixWord, tailWord_851096, baseEnd_851096] using wordTrace_append hprefix tailTrace_851096
  have hstable : (prefixWord ++ tailWord_851096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851096).length < 2 ^ (prefixWord ++ tailWord_851096).sum := by decide
  have hdescent : baseEnd_851096 < baseStart_851096 := by decide
  rcases family_descends (prefixWord ++ tailWord_851096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851100 : List Nat := [2, 2, 3, 2, 1, 3, 1, 3, 2, 3]
def baseStart_851100 : Nat := 118140960795 + 851100 * 2 ^ 59
def prefixEnd_851100 : Nat := 4983230072969 + 3 ^ 40 * 851100 * 2
def baseEnd_851100 : Nat := 291348923361150200690579

theorem tailTrace_851100 : CollatzResearch.WordTrace tailWord_851100 prefixEnd_851100 291348923361150200690579 := by
  unfold tailWord_851100
  simp only [CollatzResearch.WordTrace]
  refine ⟨15521083608308765576351377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20694778144411687435135169 15521083608308765576351377)
  ·
    refine ⟨11640812706231574182263533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15521083608308765576351377 11640812706231574182263533)
    ·
      refine ⟨4365304764836840318348825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11640812706231574182263533 4365304764836840318348825)
      ·
        refine ⟨3273978573627630238761619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4365304764836840318348825 3273978573627630238761619)
        ·
          refine ⟨4910967860441445358142429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3273978573627630238761619 4910967860441445358142429)
          ·
            refine ⟨1841612947665542009303411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4910967860441445358142429 1841612947665542009303411)
            ·
              refine ⟨2762419421498313013955117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1841612947665542009303411 2762419421498313013955117)
              ·
                refine ⟨1035907283061867380233169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2762419421498313013955117 1035907283061867380233169)
                ·
                  refine ⟨776930462296400535174877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1035907283061867380233169 776930462296400535174877)
                  ·
                    refine ⟨291348923361150200690579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 776930462296400535174877 291348923361150200690579)
                    ·
                      rfl

theorem cell22_851100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_851100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851100 prefixEnd_851100 := by exact prefixLift 851100
  have htrace : WordTrace (prefixWord ++ tailWord_851100) baseStart_851100 baseEnd_851100 := by
    simpa [prefixWord, tailWord_851100, baseEnd_851100] using wordTrace_append hprefix tailTrace_851100
  have hstable : (prefixWord ++ tailWord_851100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851100).length < 2 ^ (prefixWord ++ tailWord_851100).sum := by decide
  have hdescent : baseEnd_851100 < baseStart_851100 := by decide
  rcases family_descends (prefixWord ++ tailWord_851100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851203 : List Nat := [1, 1, 1, 3, 2, 5, 2, 1, 6]
def baseStart_851203 : Nat := 118140960795 + 851203 * 2 ^ 59
def prefixEnd_851203 : Nat := 4983230072969 + 3 ^ 40 * 851203 * 2
def baseEnd_851203 : Nat := 97128060788697421788421

theorem tailTrace_851203 : CollatzResearch.WordTrace tailWord_851203 prefixEnd_851203 97128060788697421788421 := by
  unfold tailWord_851203
  simp only [CollatzResearch.WordTrace]
  refine ⟨31045923935244379743702263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20697282623496253162468175 31045923935244379743702263)
  ·
    refine ⟨46568885902866569615553395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31045923935244379743702263 46568885902866569615553395)
    ·
      refine ⟨69853328854299854423330093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46568885902866569615553395 69853328854299854423330093)
      ·
        refine ⟨26194998320362445408748785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69853328854299854423330093 26194998320362445408748785)
        ·
          refine ⟨19646248740271834056561589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26194998320362445408748785 19646248740271834056561589)
          ·
            refine ⟨1841835819400484442802649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19646248740271834056561589 1841835819400484442802649)
            ·
              refine ⟨1381376864550363332101987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1841835819400484442802649 1381376864550363332101987)
              ·
                refine ⟨2072065296825544998152981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1381376864550363332101987 2072065296825544998152981)
                ·
                  refine ⟨97128060788697421788421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2072065296825544998152981 97128060788697421788421)
                  ·
                    rfl

theorem cell22_851203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 6].length) (baseStart_851203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851203 prefixEnd_851203 := by exact prefixLift 851203
  have htrace : WordTrace (prefixWord ++ tailWord_851203) baseStart_851203 baseEnd_851203 := by
    simpa [prefixWord, tailWord_851203, baseEnd_851203] using wordTrace_append hprefix tailTrace_851203
  have hstable : (prefixWord ++ tailWord_851203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851203).length < 2 ^ (prefixWord ++ tailWord_851203).sum := by decide
  have hdescent : baseEnd_851203 < baseStart_851203 := by decide
  rcases family_descends (prefixWord ++ tailWord_851203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851233 : List Nat := [1, 2, 3, 2, 1, 1, 1, 5, 2, 4]
def baseStart_851233 : Nat := 118140960795 + 851233 * 2 ^ 59
def prefixEnd_851233 : Nat := 4983230072969 + 3 ^ 40 * 851233 * 2
def baseEnd_851233 : Nat := 291394451979182187115171

theorem tailTrace_851233 : CollatzResearch.WordTrace tailWord_851233 prefixEnd_851233 291394451979182187115171 := by
  unfold tailWord_851233
  simp only [CollatzResearch.WordTrace]
  refine ⟨31047018125135694867294353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20698012083423796578196235 31047018125135694867294353)
  ·
    refine ⟨23285263593851771150470765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31047018125135694867294353 23285263593851771150470765)
    ·
      refine ⟨8731973847694414181426537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23285263593851771150470765 8731973847694414181426537)
      ·
        refine ⟨6548980385770810636069903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8731973847694414181426537 6548980385770810636069903)
        ·
          refine ⟨9823470578656215954104855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6548980385770810636069903 9823470578656215954104855)
          ·
            refine ⟨14735205867984323931157283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9823470578656215954104855 14735205867984323931157283)
            ·
              refine ⟨22102808801976485896735925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14735205867984323931157283 22102808801976485896735925)
              ·
                refine ⟨2072138325185295552818993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22102808801976485896735925 2072138325185295552818993)
                ·
                  refine ⟨1554103743888971664614245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2072138325185295552818993 1554103743888971664614245)
                  ·
                    refine ⟨291394451979182187115171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1554103743888971664614245 291394451979182187115171)
                    ·
                      rfl

theorem cell22_851233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_851233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851233 prefixEnd_851233 := by exact prefixLift 851233
  have htrace : WordTrace (prefixWord ++ tailWord_851233) baseStart_851233 baseEnd_851233 := by
    simpa [prefixWord, tailWord_851233, baseEnd_851233] using wordTrace_append hprefix tailTrace_851233
  have hstable : (prefixWord ++ tailWord_851233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851233).length < 2 ^ (prefixWord ++ tailWord_851233).sum := by decide
  have hdescent : baseEnd_851233 < baseStart_851233 := by decide
  rcases family_descends (prefixWord ++ tailWord_851233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851237 : List Nat := [1, 3, 1, 2, 4, 3, 1, 3, 4]
def baseStart_851237 : Nat := 118140960795 + 851237 * 2 ^ 59
def prefixEnd_851237 : Nat := 4983230072969 + 3 ^ 40 * 851237 * 2
def baseEnd_851237 : Nat := 97131940420309170005053

theorem tailTrace_851237 : CollatzResearch.WordTrace tailWord_851237 prefixEnd_851237 97131940420309170005053 := by
  unfold tailWord_851237
  simp only [CollatzResearch.WordTrace]
  refine ⟨31047164017121203550439965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20698109344747469033626643 31047164017121203550439965)
  ·
    refine ⟨11642686506420451331414987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31047164017121203550439965 11642686506420451331414987)
    ·
      refine ⟨17464029759630676997122481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11642686506420451331414987 17464029759630676997122481)
      ·
        refine ⟨13098022319723007747841861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17464029759630676997122481 13098022319723007747841861)
        ·
          refine ⟨2455879184948063952720349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13098022319723007747841861 2455879184948063952720349)
          ·
            refine ⟨920954694355523982270131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2455879184948063952720349 920954694355523982270131)
            ·
              refine ⟨1381432041533285973405197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920954694355523982270131 1381432041533285973405197)
              ·
                refine ⟨518037015574982240026949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1381432041533285973405197 518037015574982240026949)
                ·
                  refine ⟨97131940420309170005053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 518037015574982240026949 97131940420309170005053)
                  ·
                    rfl

theorem cell22_851237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_851237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851237 prefixEnd_851237 := by exact prefixLift 851237
  have htrace : WordTrace (prefixWord ++ tailWord_851237) baseStart_851237 baseEnd_851237 := by
    simpa [prefixWord, tailWord_851237, baseEnd_851237] using wordTrace_append hprefix tailTrace_851237
  have hstable : (prefixWord ++ tailWord_851237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851237).length < 2 ^ (prefixWord ++ tailWord_851237).sum := by decide
  have hdescent : baseEnd_851237 < baseStart_851237 := by decide
  rcases family_descends (prefixWord ++ tailWord_851237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851250 : List Nat := [3, 2, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_851250 : Nat := 118140960795 + 851250 * 2 ^ 59
def prefixEnd_851250 : Nat := 4983230072969 + 3 ^ 40 * 851250 * 2
def baseEnd_851250 : Nat := 291400271426599809440119

theorem tailTrace_851250 : CollatzResearch.WordTrace tailWord_851250 prefixEnd_851250 291400271426599809440119 := by
  unfold tailWord_851250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7761909541518526692665801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20698425444049404513775469 7761909541518526692665801)
  ·
    refine ⟨5821432156138895019499351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7761909541518526692665801 5821432156138895019499351)
    ·
      refine ⟨8732148234208342529249027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5821432156138895019499351 8732148234208342529249027)
      ·
        refine ⟨13098222351312513793873541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8732148234208342529249027 13098222351312513793873541)
        ·
          refine ⟨2455916690871096336351289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13098222351312513793873541 2455916690871096336351289)
          ·
            refine ⟨1841937518153322252263467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2455916690871096336351289 1841937518153322252263467)
            ·
              refine ⟨2762906277229983378395201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1841937518153322252263467 2762906277229983378395201)
              ·
                refine ⟨2072179707922487533796401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2762906277229983378395201 2072179707922487533796401)
                ·
                  refine ⟨1554134780941865650347301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2072179707922487533796401 1554134780941865650347301)
                  ·
                    refine ⟨291400271426599809440119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1554134780941865650347301 291400271426599809440119)
                    ·
                      rfl

theorem cell22_851250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_851250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851250 prefixEnd_851250 := by exact prefixLift 851250
  have htrace : WordTrace (prefixWord ++ tailWord_851250) baseStart_851250 baseEnd_851250 := by
    simpa [prefixWord, tailWord_851250, baseEnd_851250] using wordTrace_append hprefix tailTrace_851250
  have hstable : (prefixWord ++ tailWord_851250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851250).length < 2 ^ (prefixWord ++ tailWord_851250).sum := by decide
  have hdescent : baseEnd_851250 < baseStart_851250 := by decide
  rcases family_descends (prefixWord ++ tailWord_851250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851252 : List Nat := [2, 5, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_851252 : Nat := 118140960795 + 851252 * 2 ^ 59
def prefixEnd_851252 : Nat := 4983230072969 + 3 ^ 40 * 851252 * 2
def baseEnd_851252 : Nat := 291400956067472470890113

theorem tailTrace_851252 : CollatzResearch.WordTrace tailWord_851252 prefixEnd_851252 291400956067472470890113 := by
  unfold tailWord_851252
  simp only [CollatzResearch.WordTrace]
  refine ⟨15523855556033430556118005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20698474074711240741490673 15523855556033430556118005)
  ·
    refine ⟨1455361458378134114636063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15523855556033430556118005 1455361458378134114636063)
    ·
      refine ⟨2183042187567201171954095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1455361458378134114636063 2183042187567201171954095)
      ·
        refine ⟨3274563281350801757931143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2183042187567201171954095 3274563281350801757931143)
        ·
          refine ⟨4911844922026202636896715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3274563281350801757931143 4911844922026202636896715)
          ·
            refine ⟨7367767383039303955345073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4911844922026202636896715 7367767383039303955345073)
            ·
              refine ⟨5525825537279477966508805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7367767383039303955345073 5525825537279477966508805)
              ·
                refine ⟨1036092288239902118720401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5525825537279477966508805 1036092288239902118720401)
                ·
                  refine ⟨777069216179926589040301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1036092288239902118720401 777069216179926589040301)
                  ·
                    refine ⟨291400956067472470890113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 777069216179926589040301 291400956067472470890113)
                    ·
                      rfl

theorem cell22_851252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_851252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851252 prefixEnd_851252 := by exact prefixLift 851252
  have htrace : WordTrace (prefixWord ++ tailWord_851252) baseStart_851252 baseEnd_851252 := by
    simpa [prefixWord, tailWord_851252, baseEnd_851252] using wordTrace_append hprefix tailTrace_851252
  have hstable : (prefixWord ++ tailWord_851252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851252).length < 2 ^ (prefixWord ++ tailWord_851252).sum := by decide
  have hdescent : baseEnd_851252 < baseStart_851252 := by decide
  rcases family_descends (prefixWord ++ tailWord_851252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851254 : List Nat := [5, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_851254 : Nat := 118140960795 + 851254 * 2 ^ 59
def prefixEnd_851254 : Nat := 4983230072969 + 3 ^ 40 * 851254 * 2
def baseEnd_851254 : Nat := 97133880236115044113369

theorem tailTrace_851254 : CollatzResearch.WordTrace tailWord_851254 prefixEnd_851254 97133880236115044113369 := by
  unfold tailWord_851254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1940486503628725965863051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20698522705373076969205877 1940486503628725965863051)
  ·
    refine ⟨2910729755443088948794577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1940486503628725965863051 2910729755443088948794577)
    ·
      refine ⟨2183047316582316711595933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2910729755443088948794577 2183047316582316711595933)
      ·
        refine ⟨818642743718368766848475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2183047316582316711595933 818642743718368766848475)
        ·
          refine ⟨1227964115577553150272713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818642743718368766848475 1227964115577553150272713)
          ·
            refine ⟨920973086683164862704535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1227964115577553150272713 920973086683164862704535)
            ·
              refine ⟨1381459630024747294056803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920973086683164862704535 1381459630024747294056803)
              ·
                refine ⟨2072189445037120941085205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1381459630024747294056803 2072189445037120941085205)
                ·
                  refine ⟨97133880236115044113369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2072189445037120941085205 97133880236115044113369)
                  ·
                    rfl

theorem cell22_851254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_851254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851254 prefixEnd_851254 := by exact prefixLift 851254
  have htrace : WordTrace (prefixWord ++ tailWord_851254) baseStart_851254 baseEnd_851254 := by
    simpa [prefixWord, tailWord_851254, baseEnd_851254] using wordTrace_append hprefix tailTrace_851254
  have hstable : (prefixWord ++ tailWord_851254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851254).length < 2 ^ (prefixWord ++ tailWord_851254).sum := by decide
  have hdescent : baseEnd_851254 < baseStart_851254 := by decide
  rcases family_descends (prefixWord ++ tailWord_851254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851265 : List Nat := [1, 2, 5, 2, 1, 2, 2, 7]
def baseStart_851265 : Nat := 118140960795 + 851265 * 2 ^ 59
def prefixEnd_851265 : Nat := 4983230072969 + 3 ^ 40 * 851265 * 2
def baseEnd_851265 : Nat := 32378378470349418923897

theorem tailTrace_851265 : CollatzResearch.WordTrace tailWord_851265 prefixEnd_851265 32378378470349418923897 := by
  unfold tailWord_851265
  simp only [CollatzResearch.WordTrace]
  refine ⟨31048185261019764332459249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20698790174013176221639499 31048185261019764332459249)
  ·
    refine ⟨23286138945764823249344437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31048185261019764332459249 23286138945764823249344437)
    ·
      refine ⟨2183075526165452179626041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23286138945764823249344437 2183075526165452179626041)
      ·
        refine ⟨1637306644624089134719531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2183075526165452179626041 1637306644624089134719531)
        ·
          refine ⟨2455959966936133702079297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1637306644624089134719531 2455959966936133702079297)
          ·
            refine ⟨1841969975202100276559473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2455959966936133702079297 1841969975202100276559473)
            ·
              refine ⟨1381477481401575207419605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1841969975202100276559473 1381477481401575207419605)
              ·
                refine ⟨32378378470349418923897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1381477481401575207419605 32378378470349418923897)
                ·
                  rfl

theorem cell22_851265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 7].length) (baseStart_851265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851265 prefixEnd_851265 := by exact prefixLift 851265
  have htrace : WordTrace (prefixWord ++ tailWord_851265) baseStart_851265 baseEnd_851265 := by
    simpa [prefixWord, tailWord_851265, baseEnd_851265] using wordTrace_append hprefix tailTrace_851265
  have hstable : (prefixWord ++ tailWord_851265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851265).length < 2 ^ (prefixWord ++ tailWord_851265).sum := by decide
  have hdescent : baseEnd_851265 < baseStart_851265 := by decide
  rcases family_descends (prefixWord ++ tailWord_851265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851286 : List Nat := [5, 2, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_851286 : Nat := 118140960795 + 851286 * 2 ^ 59
def prefixEnd_851286 : Nat := 4983230072969 + 3 ^ 40 * 851286 * 2
def baseEnd_851286 : Nat := 291412594962307715540009

theorem tailTrace_851286 : CollatzResearch.WordTrace tailWord_851286 prefixEnd_851286 291412594962307715540009 := by
  unfold tailWord_851286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1940559449621480307435857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20699300795962456612649141 1940559449621480307435857)
  ·
    refine ⟨1455419587216110230576893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1940559449621480307435857 1455419587216110230576893)
    ·
      refine ⟨545782345206041336466335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1455419587216110230576893 545782345206041336466335)
      ·
        refine ⟨818673517809062004699503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545782345206041336466335 818673517809062004699503)
        ·
          refine ⟨1228010276713593007049255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818673517809062004699503 1228010276713593007049255)
          ·
            refine ⟨1842015415070389510573883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228010276713593007049255 1842015415070389510573883)
            ·
              refine ⟨2763023122605584265860825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1842015415070389510573883 2763023122605584265860825)
              ·
                refine ⟨2072267341954188199395619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2763023122605584265860825 2072267341954188199395619)
                ·
                  refine ⟨3108401012931282299093429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2072267341954188199395619 3108401012931282299093429)
                  ·
                    refine ⟨291412594962307715540009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3108401012931282299093429 291412594962307715540009)
                    ·
                      rfl

theorem cell22_851286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_851286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851286 prefixEnd_851286 := by exact prefixLift 851286
  have htrace : WordTrace (prefixWord ++ tailWord_851286) baseStart_851286 baseEnd_851286 := by
    simpa [prefixWord, tailWord_851286, baseEnd_851286] using wordTrace_append hprefix tailTrace_851286
  have hstable : (prefixWord ++ tailWord_851286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851286).length < 2 ^ (prefixWord ++ tailWord_851286).sum := by decide
  have hdescent : baseEnd_851286 < baseStart_851286 := by decide
  rcases family_descends (prefixWord ++ tailWord_851286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851323 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 5, 4]
def baseStart_851323 : Nat := 118140960795 + 851323 * 2 ^ 59
def prefixEnd_851323 : Nat := 4983230072969 + 3 ^ 40 * 851323 * 2
def baseEnd_851323 : Nat := 291425260818451952364895

theorem tailTrace_851323 : CollatzResearch.WordTrace tailWord_851323 prefixEnd_851323 291425260818451952364895 := by
  unfold tailWord_851323
  simp only [CollatzResearch.WordTrace]
  refine ⟨31050300694809640238070623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20700200463206426825380415 31050300694809640238070623)
  ·
    refine ⟨46575451042214460357105935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31050300694809640238070623 46575451042214460357105935)
    ·
      refine ⟨69863176563321690535658903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46575451042214460357105935 69863176563321690535658903)
      ·
        refine ⟨104794764844982535803488355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69863176563321690535658903 104794764844982535803488355)
        ·
          refine ⟨157192147267473803705232533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104794764844982535803488355 157192147267473803705232533)
          ·
            refine ⟨7368381903162834548682775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 157192147267473803705232533 7368381903162834548682775)
            ·
              refine ⟨11052572854744251823024163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7368381903162834548682775 11052572854744251823024163)
              ·
                refine ⟨16578859282116377734536245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11052572854744251823024163 16578859282116377734536245)
                ·
                  refine ⟨1554268057698410412612773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16578859282116377734536245 1554268057698410412612773)
                  ·
                    refine ⟨291425260818451952364895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1554268057698410412612773 291425260818451952364895)
                    ·
                      rfl

theorem cell22_851323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 4].length) (baseStart_851323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851323 prefixEnd_851323 := by exact prefixLift 851323
  have htrace : WordTrace (prefixWord ++ tailWord_851323) baseStart_851323 baseEnd_851323 := by
    simpa [prefixWord, tailWord_851323, baseEnd_851323] using wordTrace_append hprefix tailTrace_851323
  have hstable : (prefixWord ++ tailWord_851323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851323).length < 2 ^ (prefixWord ++ tailWord_851323).sum := by decide
  have hdescent : baseEnd_851323 < baseStart_851323 := by decide
  rcases family_descends (prefixWord ++ tailWord_851323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851340 : List Nat := [2, 2, 1, 2, 1, 3, 2, 4, 1, 4]
def baseStart_851340 : Nat := 118140960795 + 851340 * 2 ^ 59
def prefixEnd_851340 : Nat := 4983230072969 + 3 ^ 40 * 851340 * 2
def baseEnd_851340 : Nat := 291431080265869574689843

theorem tailTrace_851340 : CollatzResearch.WordTrace tailWord_851340 prefixEnd_851340 291431080265869574689843 := by
  unfold tailWord_851340
  simp only [CollatzResearch.WordTrace]
  refine ⟨15525460367874026070719737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20700613823832034760959649 15525460367874026070719737)
  ·
    refine ⟨11644095275905519553039803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15525460367874026070719737 11644095275905519553039803)
    ·
      refine ⟨17466142913858279329559705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11644095275905519553039803 17466142913858279329559705)
      ·
        refine ⟨13099607185393709497169779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17466142913858279329559705 13099607185393709497169779)
        ·
          refine ⟨19649410778090564245754669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13099607185393709497169779 19649410778090564245754669)
          ·
            refine ⟨7368529041783961592158001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19649410778090564245754669 7368529041783961592158001)
            ·
              refine ⟨5526396781337971194118501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7368529041783961592158001 5526396781337971194118501)
              ·
                refine ⟨1036199396500869598897219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5526396781337971194118501 1036199396500869598897219)
                ·
                  refine ⟨1554299094751304398345829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036199396500869598897219 1554299094751304398345829)
                  ·
                    refine ⟨291431080265869574689843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1554299094751304398345829 291431080265869574689843)
                    ·
                      rfl

theorem cell22_851340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_851340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851340 prefixEnd_851340 := by exact prefixLift 851340
  have htrace : WordTrace (prefixWord ++ tailWord_851340) baseStart_851340 baseEnd_851340 := by
    simpa [prefixWord, tailWord_851340, baseEnd_851340] using wordTrace_append hprefix tailTrace_851340
  have hstable : (prefixWord ++ tailWord_851340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851340).length < 2 ^ (prefixWord ++ tailWord_851340).sum := by decide
  have hdescent : baseEnd_851340 < baseStart_851340 := by decide
  rcases family_descends (prefixWord ++ tailWord_851340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851357 : List Nat := [1, 4, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_851357 : Nat := 118140960795 + 851357 * 2 ^ 59
def prefixEnd_851357 : Nat := 4983230072969 + 3 ^ 40 * 851357 * 2
def baseEnd_851357 : Nat := 291436899713287197014791

theorem tailTrace_851357 : CollatzResearch.WordTrace tailWord_851357 prefixEnd_851357 291436899713287197014791 := by
  unfold tailWord_851357
  simp only [CollatzResearch.WordTrace]
  refine ⟨31051540776686464044808325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20701027184457642696538883 31051540776686464044808325)
  ·
    refine ⟨5822163895628712008401561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31051540776686464044808325 5822163895628712008401561)
    ·
      refine ⟨4366622921721534006301171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5822163895628712008401561 4366622921721534006301171)
      ·
        refine ⟨6549934382582301009451757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4366622921721534006301171 6549934382582301009451757)
        ·
          refine ⟨2456225393468362878544409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6549934382582301009451757 2456225393468362878544409)
          ·
            refine ⟨1842169045101272158908307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2456225393468362878544409 1842169045101272158908307)
            ·
              refine ⟨2763253567651908238362461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1842169045101272158908307 2763253567651908238362461)
              ·
                refine ⟨1036220087869465589385923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2763253567651908238362461 1036220087869465589385923)
                ·
                  refine ⟨1554330131804198384078885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036220087869465589385923 1554330131804198384078885)
                  ·
                    refine ⟨291436899713287197014791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1554330131804198384078885 291436899713287197014791)
                    ·
                      rfl

theorem cell22_851357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_851357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851357 prefixEnd_851357 := by exact prefixLift 851357
  have htrace : WordTrace (prefixWord ++ tailWord_851357) baseStart_851357 baseEnd_851357 := by
    simpa [prefixWord, tailWord_851357, baseEnd_851357] using wordTrace_append hprefix tailTrace_851357
  have hstable : (prefixWord ++ tailWord_851357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851357).length < 2 ^ (prefixWord ++ tailWord_851357).sum := by decide
  have hdescent : baseEnd_851357 < baseStart_851357 := by decide
  rcases family_descends (prefixWord ++ tailWord_851357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851383 : List Nat := [1, 1, 3, 1, 3, 2, 2, 9]
def baseStart_851383 : Nat := 118140960795 + 851383 * 2 ^ 59
def prefixEnd_851383 : Nat := 4983230072969 + 3 ^ 40 * 851383 * 2
def baseEnd_851383 : Nat := 32382866671625755096079

theorem tailTrace_851383 : CollatzResearch.WordTrace tailWord_851383 prefixEnd_851383 32382866671625755096079 := by
  unfold tailWord_851383
  simp only [CollatzResearch.WordTrace]
  refine ⟨31052489074592270485254803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20701659383061513656836535 31052489074592270485254803)
  ·
    refine ⟨46578733611888405727882205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31052489074592270485254803 46578733611888405727882205)
    ·
      refine ⟨17467025104458152147955827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46578733611888405727882205 17467025104458152147955827)
      ·
        refine ⟨26200537656687228221933741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17467025104458152147955827 26200537656687228221933741)
        ·
          refine ⟨9825201621257710583225153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26200537656687228221933741 9825201621257710583225153)
          ·
            refine ⟨7368901215943282937418865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9825201621257710583225153 7368901215943282937418865)
            ·
              refine ⟨5526675911957462203064149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7368901215943282937418865 5526675911957462203064149)
              ·
                refine ⟨32382866671625755096079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5526675911957462203064149 32382866671625755096079)
                ·
                  rfl

theorem cell22_851383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 9].length) (baseStart_851383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851383 prefixEnd_851383 := by exact prefixLift 851383
  have htrace : WordTrace (prefixWord ++ tailWord_851383) baseStart_851383 baseEnd_851383 := by
    simpa [prefixWord, tailWord_851383, baseEnd_851383] using wordTrace_append hprefix tailTrace_851383
  have hstable : (prefixWord ++ tailWord_851383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851383).length < 2 ^ (prefixWord ++ tailWord_851383).sum := by decide
  have hdescent : baseEnd_851383 < baseStart_851383 := by decide
  rcases family_descends (prefixWord ++ tailWord_851383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851415 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 5, 3]
def baseStart_851415 : Nat := 118140960795 + 851415 * 2 ^ 59
def prefixEnd_851415 : Nat := 4983230072969 + 3 ^ 40 * 851415 * 2
def baseEnd_851415 : Nat := 291456754298594379064613

theorem tailTrace_851415 : CollatzResearch.WordTrace tailWord_851415 prefixEnd_851415 291456754298594379064613 := by
  unfold tailWord_851415
  simp only [CollatzResearch.WordTrace]
  refine ⟨31053656210476339950419699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20702437473650893300279799 31053656210476339950419699)
  ·
    refine ⟨46580484315714509925629549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31053656210476339950419699 46580484315714509925629549)
    ·
      refine ⟨17467681618392941222111081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46580484315714509925629549 17467681618392941222111081)
      ·
        refine ⟨13100761213794705916583311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17467681618392941222111081 13100761213794705916583311)
        ·
          refine ⟨19651141820692058874874967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13100761213794705916583311 19651141820692058874874967)
          ·
            refine ⟨29476712731038088312312451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19651141820692058874874967 29476712731038088312312451)
            ·
              refine ⟨44215069096557132468468677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29476712731038088312312451 44215069096557132468468677)
              ·
                refine ⟨8290325455604462337837877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44215069096557132468468677 8290325455604462337837877)
                ·
                  refine ⟨777218011462918344172301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8290325455604462337837877 777218011462918344172301)
                  ·
                    refine ⟨291456754298594379064613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 777218011462918344172301 291456754298594379064613)
                    ·
                      rfl

theorem cell22_851415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_851415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851415 prefixEnd_851415 := by exact prefixLift 851415
  have htrace : WordTrace (prefixWord ++ tailWord_851415) baseStart_851415 baseEnd_851415 := by
    simpa [prefixWord, tailWord_851415, baseEnd_851415] using wordTrace_append hprefix tailTrace_851415
  have hstable : (prefixWord ++ tailWord_851415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851415).length < 2 ^ (prefixWord ++ tailWord_851415).sum := by decide
  have hdescent : baseEnd_851415 < baseStart_851415 := by decide
  rcases family_descends (prefixWord ++ tailWord_851415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851556 : List Nat := [2, 3, 1, 1, 2, 4, 3, 1, 2, 3]
def baseStart_851556 : Nat := 118140960795 + 851556 * 2 ^ 59
def prefixEnd_851556 : Nat := 4983230072969 + 3 ^ 40 * 851556 * 2
def baseEnd_851556 : Nat := 291505021480117011289181

theorem tailTrace_851556 : CollatzResearch.WordTrace tailWord_851556 prefixEnd_851556 291505021480117011289181 := by
  unfold tailWord_851556
  simp only [CollatzResearch.WordTrace]
  refine ⟨15529399451482760515651261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20705865935310347354201681 15529399451482760515651261)
  ·
    refine ⟨5823524794306035193369223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15529399451482760515651261 5823524794306035193369223)
    ·
      refine ⟨8735287191459052790053835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5823524794306035193369223 8735287191459052790053835)
      ·
        refine ⟨13102930787188579185080753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8735287191459052790053835 13102930787188579185080753)
        ·
          refine ⟨9827198090391434388810565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13102930787188579185080753 9827198090391434388810565)
          ·
            refine ⟨1842599641948393947901981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9827198090391434388810565 1842599641948393947901981)
            ·
              refine ⟨690974865730647730463243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1842599641948393947901981 690974865730647730463243)
              ·
                refine ⟨1036462298595971595694865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 690974865730647730463243 1036462298595971595694865)
                ·
                  refine ⟨777346723946978696771149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1036462298595971595694865 777346723946978696771149)
                  ·
                    refine ⟨291505021480117011289181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 777346723946978696771149 291505021480117011289181)
                    ·
                      rfl

theorem cell22_851556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_851556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851556 prefixEnd_851556 := by exact prefixLift 851556
  have htrace : WordTrace (prefixWord ++ tailWord_851556) baseStart_851556 baseEnd_851556 := by
    simpa [prefixWord, tailWord_851556, baseEnd_851556] using wordTrace_append hprefix tailTrace_851556
  have hstable : (prefixWord ++ tailWord_851556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851556).length < 2 ^ (prefixWord ++ tailWord_851556).sum := by decide
  have hdescent : baseEnd_851556 < baseStart_851556 := by decide
  rcases family_descends (prefixWord ++ tailWord_851556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851661 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_851661 : Nat := 118140960795 + 851661 * 2 ^ 59
def prefixEnd_851661 : Nat := 4983230072969 + 3 ^ 40 * 851661 * 2
def baseEnd_851661 : Nat := 291540965125931737413859

theorem tailTrace_851661 : CollatzResearch.WordTrace tailWord_851661 prefixEnd_851661 291540965125931737413859 := by
  unfold tailWord_851661
  simp only [CollatzResearch.WordTrace]
  refine ⟨31062628567585123963874837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20708419045056749309249891 31062628567585123963874837)
  ·
    refine ⟨1456060714105552685806633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31062628567585123963874837 1456060714105552685806633)
    ·
      refine ⟨1092045535579164514354975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1456060714105552685806633 1092045535579164514354975)
      ·
        refine ⟨1638068303368746771532463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092045535579164514354975 1638068303368746771532463)
        ·
          refine ⟨2457102455053120157298695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1638068303368746771532463 2457102455053120157298695)
          ·
            refine ⟨3685653682579680235948043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2457102455053120157298695 3685653682579680235948043)
            ·
              refine ⟨5528480523869520353922065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3685653682579680235948043 5528480523869520353922065)
              ·
                refine ⟨4146360392902140265441549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5528480523869520353922065 4146360392902140265441549)
                ·
                  refine ⟨1554885147338302599540581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4146360392902140265441549 1554885147338302599540581)
                  ·
                    refine ⟨291540965125931737413859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1554885147338302599540581 291540965125931737413859)
                    ·
                      rfl

theorem cell22_851661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_851661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851661 prefixEnd_851661 := by exact prefixLift 851661
  have htrace : WordTrace (prefixWord ++ tailWord_851661) baseStart_851661 baseEnd_851661 := by
    simpa [prefixWord, tailWord_851661, baseEnd_851661] using wordTrace_append hprefix tailTrace_851661
  have hstable : (prefixWord ++ tailWord_851661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851661).length < 2 ^ (prefixWord ++ tailWord_851661).sum := by decide
  have hdescent : baseEnd_851661 < baseStart_851661 := by decide
  rcases family_descends (prefixWord ++ tailWord_851661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851672 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 1, 6]
def baseStart_851672 : Nat := 118140960795 + 851672 * 2 ^ 59
def prefixEnd_851672 : Nat := 4983230072969 + 3 ^ 40 * 851672 * 2
def baseEnd_851672 : Nat := 291544730650731375388825

theorem tailTrace_851672 : CollatzResearch.WordTrace tailWord_851672 prefixEnd_851672 291544730650731375388825 := by
  unfold tailWord_851672
  simp only [CollatzResearch.WordTrace]
  refine ⟨15531514885272636421262635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20708686513696848561683513 15531514885272636421262635)
  ·
    refine ⟨23297272327908954631893953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15531514885272636421262635 23297272327908954631893953)
    ·
      refine ⟨17472954245931715973920465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23297272327908954631893953 17472954245931715973920465)
      ·
        refine ⟨13104715684448786980440349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17472954245931715973920465 13104715684448786980440349)
        ·
          refine ⟨4914268381668295117665131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13104715684448786980440349 4914268381668295117665131)
          ·
            refine ⟨7371402572502442676497697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4914268381668295117665131 7371402572502442676497697)
            ·
              refine ⟨5528551929376832007373273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7371402572502442676497697 5528551929376832007373273)
              ·
                refine ⟨4146413947032624005529955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5528551929376832007373273 4146413947032624005529955)
                ·
                  refine ⟨6219620920548936008294933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4146413947032624005529955 6219620920548936008294933)
                  ·
                    refine ⟨291544730650731375388825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6219620920548936008294933 291544730650731375388825)
                    ·
                      rfl

theorem cell22_851672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_851672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851672 prefixEnd_851672 := by exact prefixLift 851672
  have htrace : WordTrace (prefixWord ++ tailWord_851672) baseStart_851672 baseEnd_851672 := by
    simpa [prefixWord, tailWord_851672, baseEnd_851672] using wordTrace_append hprefix tailTrace_851672
  have hstable : (prefixWord ++ tailWord_851672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851672).length < 2 ^ (prefixWord ++ tailWord_851672).sum := by decide
  have hdescent : baseEnd_851672 < baseStart_851672 := by decide
  rcases family_descends (prefixWord ++ tailWord_851672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851674 : List Nat := [3, 1, 1, 2, 2, 4, 2, 1, 1, 5]
def baseStart_851674 : Nat := 118140960795 + 851674 * 2 ^ 59
def prefixEnd_851674 : Nat := 4983230072969 + 3 ^ 40 * 851674 * 2
def baseEnd_851674 : Nat := 291545415291604036838819

theorem tailTrace_851674 : CollatzResearch.WordTrace tailWord_851674 prefixEnd_851674 291545415291604036838819 := by
  unfold tailWord_851674
  simp only [CollatzResearch.WordTrace]
  refine ⟨7765775679134506796024519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20708735144358684789398717 7765775679134506796024519)
  ·
    refine ⟨11648663518701760194036779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7765775679134506796024519 11648663518701760194036779)
    ·
      refine ⟨17472995278052640291055169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11648663518701760194036779 17472995278052640291055169)
      ·
        refine ⟨13104746458539480218291377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17472995278052640291055169 13104746458539480218291377)
        ·
          refine ⟨9828559843904610163718533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13104746458539480218291377 9828559843904610163718533)
          ·
            refine ⟨1842854970732114405697225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9828559843904610163718533 1842854970732114405697225)
            ·
              refine ⟨1382141228049085804272919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1842854970732114405697225 1382141228049085804272919)
              ·
                refine ⟨2073211842073628706409379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1382141228049085804272919 2073211842073628706409379)
                ·
                  refine ⟨3109817763110443059614069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2073211842073628706409379 3109817763110443059614069)
                  ·
                    refine ⟨291545415291604036838819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3109817763110443059614069 291545415291604036838819)
                    ·
                      rfl

theorem cell22_851674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_851674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851674 prefixEnd_851674 := by exact prefixLift 851674
  have htrace : WordTrace (prefixWord ++ tailWord_851674) baseStart_851674 baseEnd_851674 := by
    simpa [prefixWord, tailWord_851674, baseEnd_851674] using wordTrace_append hprefix tailTrace_851674
  have hstable : (prefixWord ++ tailWord_851674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851674).length < 2 ^ (prefixWord ++ tailWord_851674).sum := by decide
  have hdescent : baseEnd_851674 < baseStart_851674 := by decide
  rcases family_descends (prefixWord ++ tailWord_851674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851676 : List Nat := [2, 2, 5, 1, 2, 1, 1, 2, 6]
def baseStart_851676 : Nat := 118140960795 + 851676 * 2 ^ 59
def prefixEnd_851676 : Nat := 4983230072969 + 3 ^ 40 * 851676 * 2
def baseEnd_851676 : Nat := 97182033310825566096271

theorem tailTrace_851676 : CollatzResearch.WordTrace tailWord_851676 prefixEnd_851676 97182033310825566096271 := by
  unfold tailWord_851676
  simp only [CollatzResearch.WordTrace]
  refine ⟨15531587831265390762835441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20708783775020521017113921 15531587831265390762835441)
  ·
    refine ⟨11648690873449043072126581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15531587831265390762835441 11648690873449043072126581)
    ·
      refine ⟨1092064769385847788011867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11648690873449043072126581 1092064769385847788011867)
      ·
        refine ⟨1638097154078771682017801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092064769385847788011867 1638097154078771682017801)
        ·
          refine ⟨1228572865559078761513351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1638097154078771682017801 1228572865559078761513351)
          ·
            refine ⟨1842859298338618142270027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228572865559078761513351 1842859298338618142270027)
            ·
              refine ⟨2764288947507927213405041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1842859298338618142270027 2764288947507927213405041)
              ·
                refine ⟨2073216710630945410053781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2764288947507927213405041 2073216710630945410053781)
                ·
                  refine ⟨97182033310825566096271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2073216710630945410053781 97182033310825566096271)
                  ·
                    rfl

theorem cell22_851676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_851676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851676 prefixEnd_851676 := by exact prefixLift 851676
  have htrace : WordTrace (prefixWord ++ tailWord_851676) baseStart_851676 baseEnd_851676 := by
    simpa [prefixWord, tailWord_851676, baseEnd_851676] using wordTrace_append hprefix tailTrace_851676
  have hstable : (prefixWord ++ tailWord_851676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851676).length < 2 ^ (prefixWord ++ tailWord_851676).sum := by decide
  have hdescent : baseEnd_851676 < baseStart_851676 := by decide
  rcases family_descends (prefixWord ++ tailWord_851676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851747 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 1, 7]
def baseStart_851747 : Nat := 118140960795 + 851747 * 2 ^ 59
def prefixEnd_851747 : Nat := 4983230072969 + 3 ^ 40 * 851747 * 2
def baseEnd_851747 : Nat := 291570404683456179763595

theorem tailTrace_851747 : CollatzResearch.WordTrace tailWord_851747 prefixEnd_851747 291570404683456179763595 := by
  unfold tailWord_851747
  simp only [CollatzResearch.WordTrace]
  refine ⟨31065765245273560651505495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20710510163515707101003663 31065765245273560651505495)
  ·
    refine ⟨46598647867910340977258243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31065765245273560651505495 46598647867910340977258243)
    ·
      refine ⟨69897971801865511465887365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46598647867910340977258243 69897971801865511465887365)
      ·
        refine ⟨13105869712849783399853881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69897971801865511465887365 13105869712849783399853881)
        ·
          refine ⟨9829402284637337549890411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13105869712849783399853881 9829402284637337549890411)
          ·
            refine ⟨14744103426956006324835617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9829402284637337549890411 14744103426956006324835617)
            ·
              refine ⟨11058077570217004743626713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14744103426956006324835617 11058077570217004743626713)
              ·
                refine ⟨8293558177662753557720035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11058077570217004743626713 8293558177662753557720035)
                ·
                  refine ⟨12440337266494130336580053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8293558177662753557720035 12440337266494130336580053)
                  ·
                    refine ⟨291570404683456179763595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12440337266494130336580053 291570404683456179763595)
                    ·
                      rfl

theorem cell22_851747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 7].length) (baseStart_851747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851747 prefixEnd_851747 := by exact prefixLift 851747
  have htrace : WordTrace (prefixWord ++ tailWord_851747) baseStart_851747 baseEnd_851747 := by
    simpa [prefixWord, tailWord_851747, baseEnd_851747] using wordTrace_append hprefix tailTrace_851747
  have hstable : (prefixWord ++ tailWord_851747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851747).length < 2 ^ (prefixWord ++ tailWord_851747).sum := by decide
  have hdescent : baseEnd_851747 < baseStart_851747 := by decide
  rcases family_descends (prefixWord ++ tailWord_851747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851766 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_851766 : Nat := 118140960795 + 851766 * 2 ^ 59
def prefixEnd_851766 : Nat := 4983230072969 + 3 ^ 40 * 851766 * 2
def baseEnd_851766 : Nat := 97192302923915487846179

theorem tailTrace_851766 : CollatzResearch.WordTrace tailWord_851766 prefixEnd_851766 97192302923915487846179 := by
  unfold tailWord_851766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1941653639512795431027947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20710972154803151264298101 1941653639512795431027947)
  ·
    refine ⟨2912480459269193146541921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1941653639512795431027947 2912480459269193146541921)
    ·
      refine ⟨2184360344451894859906441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2912480459269193146541921 2184360344451894859906441)
      ·
        refine ⟨1638270258338921144929831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2184360344451894859906441 1638270258338921144929831)
        ·
          refine ⟨2457405387508381717394747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1638270258338921144929831 2457405387508381717394747)
          ·
            refine ⟨3686108081262572576092121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2457405387508381717394747 3686108081262572576092121)
            ·
              refine ⟨2764581060946929432069091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3686108081262572576092121 2764581060946929432069091)
              ·
                refine ⟨4146871591420394148103637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2764581060946929432069091 4146871591420394148103637)
                ·
                  refine ⟨97192302923915487846179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4146871591420394148103637 97192302923915487846179)
                  ·
                    rfl

theorem cell22_851766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_851766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851766 prefixEnd_851766 := by exact prefixLift 851766
  have htrace : WordTrace (prefixWord ++ tailWord_851766) baseStart_851766 baseEnd_851766 := by
    simpa [prefixWord, tailWord_851766, baseEnd_851766] using wordTrace_append hprefix tailTrace_851766
  have hstable : (prefixWord ++ tailWord_851766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851766).length < 2 ^ (prefixWord ++ tailWord_851766).sum := by decide
  have hdescent : baseEnd_851766 < baseStart_851766 := by decide
  rcases family_descends (prefixWord ++ tailWord_851766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851770 : List Nat := [3, 1, 1, 1, 5, 2, 3, 2, 1, 3]
def baseStart_851770 : Nat := 118140960795 + 851770 * 2 ^ 59
def prefixEnd_851770 : Nat := 4983230072969 + 3 ^ 40 * 851770 * 2
def baseEnd_851770 : Nat := 291578278053491786438525

theorem tailTrace_851770 : CollatzResearch.WordTrace tailWord_851770 prefixEnd_851770 291578278053491786438525 := by
  unfold tailWord_851770
  simp only [CollatzResearch.WordTrace]
  refine ⟨7766651031047558894898191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20711069416126823719728509 7766651031047558894898191)
  ·
    refine ⟨11649976546571338342347287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7766651031047558894898191 11649976546571338342347287)
    ·
      refine ⟨17474964819857007513520931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11649976546571338342347287 17474964819857007513520931)
      ·
        refine ⟨26212447229785511270281397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17474964819857007513520931 26212447229785511270281397)
        ·
          refine ⟨2457416927792391681588881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26212447229785511270281397 2457416927792391681588881)
          ·
            refine ⟨1843062695844293761191661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2457416927792391681588881 1843062695844293761191661)
            ·
              refine ⟨691148510941610160446873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1843062695844293761191661 691148510941610160446873)
              ·
                refine ⟨518361383206207620335155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 691148510941610160446873 518361383206207620335155)
                ·
                  refine ⟨777542074809311430502733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 518361383206207620335155 777542074809311430502733)
                  ·
                    refine ⟨291578278053491786438525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 777542074809311430502733 291578278053491786438525)
                    ·
                      rfl

theorem cell22_851770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 1, 3].length) (baseStart_851770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851770 prefixEnd_851770 := by exact prefixLift 851770
  have htrace : WordTrace (prefixWord ++ tailWord_851770) baseStart_851770 baseEnd_851770 := by
    simpa [prefixWord, tailWord_851770, baseEnd_851770] using wordTrace_append hprefix tailTrace_851770
  have hstable : (prefixWord ++ tailWord_851770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851770).length < 2 ^ (prefixWord ++ tailWord_851770).sum := by decide
  have hdescent : baseEnd_851770 < baseStart_851770 := by decide
  rcases family_descends (prefixWord ++ tailWord_851770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851796 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_851796 : Nat := 118140960795 + 851796 * 2 ^ 59
def prefixEnd_851796 : Nat := 4983230072969 + 3 ^ 40 * 851796 * 2
def baseEnd_851796 : Nat := 291587178384836385288445

theorem tailTrace_851796 : CollatzResearch.WordTrace tailWord_851796 prefixEnd_851796 291587178384836385288445 := by
  unfold tailWord_851796
  simp only [CollatzResearch.WordTrace]
  refine ⟨15533776211048021010019621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20711701614730694680026161 15533776211048021010019621)
  ·
    refine ⟨2912583039571503939378679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15533776211048021010019621 2912583039571503939378679)
    ·
      refine ⟨4368874559357255909068019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2912583039571503939378679 4368874559357255909068019)
      ·
        refine ⟨6553311839035883863602029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4368874559357255909068019 6553311839035883863602029)
        ·
          refine ⟨2457491939638456448850761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6553311839035883863602029 2457491939638456448850761)
          ·
            refine ⟨1843118954728842336638071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2457491939638456448850761 1843118954728842336638071)
            ·
              refine ⟨2764678432093263504957107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1843118954728842336638071 2764678432093263504957107)
              ·
                refine ⟨4147017648139895257435661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2764678432093263504957107 4147017648139895257435661)
                ·
                  refine ⟨1555131618052460721538373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4147017648139895257435661 1555131618052460721538373)
                  ·
                    refine ⟨291587178384836385288445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1555131618052460721538373 291587178384836385288445)
                    ·
                      rfl

theorem cell22_851796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_851796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851796 prefixEnd_851796 := by exact prefixLift 851796
  have htrace : WordTrace (prefixWord ++ tailWord_851796) baseStart_851796 baseEnd_851796 := by
    simpa [prefixWord, tailWord_851796, baseEnd_851796] using wordTrace_append hprefix tailTrace_851796
  have hstable : (prefixWord ++ tailWord_851796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851796).length < 2 ^ (prefixWord ++ tailWord_851796).sum := by decide
  have hdescent : baseEnd_851796 < baseStart_851796 := by decide
  rcases family_descends (prefixWord ++ tailWord_851796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851809 : List Nat := [1, 2, 3, 1, 1, 1, 5, 2, 1, 5]
def baseStart_851809 : Nat := 118140960795 + 851809 * 2 ^ 59
def prefixEnd_851809 : Nat := 4983230072969 + 3 ^ 40 * 851809 * 2
def baseEnd_851809 : Nat := 291591628550508684713405

theorem tailTrace_851809 : CollatzResearch.WordTrace tailWord_851809 prefixEnd_851809 291591628550508684713405 := by
  unfold tailWord_851809
  simp only [CollatzResearch.WordTrace]
  refine ⟨31068026571048945240262481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20712017714032630160174987 31068026571048945240262481)
  ·
    refine ⟨23301019928286708930196861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31068026571048945240262481 23301019928286708930196861)
    ·
      refine ⟨8737882473107515848823823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23301019928286708930196861 8737882473107515848823823)
      ·
        refine ⟨13106823709661273773235735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8737882473107515848823823 13106823709661273773235735)
        ·
          refine ⟨19660235564491910659853603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13106823709661273773235735 19660235564491910659853603)
          ·
            refine ⟨29490353346737865989780405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19660235564491910659853603 29490353346737865989780405)
            ·
              refine ⟨2764720626256674936541913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29490353346737865989780405 2764720626256674936541913)
              ·
                refine ⟨2073540469692506202406435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2764720626256674936541913 2073540469692506202406435)
                ·
                  refine ⟨3110310704538759303609653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2073540469692506202406435 3110310704538759303609653)
                  ·
                    refine ⟨291591628550508684713405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3110310704538759303609653 291591628550508684713405)
                    ·
                      rfl

theorem cell22_851809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_851809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851809 prefixEnd_851809 := by exact prefixLift 851809
  have htrace : WordTrace (prefixWord ++ tailWord_851809) baseStart_851809 baseEnd_851809 := by
    simpa [prefixWord, tailWord_851809, baseEnd_851809] using wordTrace_append hprefix tailTrace_851809
  have hstable : (prefixWord ++ tailWord_851809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851809).length < 2 ^ (prefixWord ++ tailWord_851809).sum := by decide
  have hdescent : baseEnd_851809 < baseStart_851809 := by decide
  rcases family_descends (prefixWord ++ tailWord_851809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851858 : List Nat := [3, 2, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_851858 : Nat := 118140960795 + 851858 * 2 ^ 59
def prefixEnd_851858 : Nat := 4983230072969 + 3 ^ 40 * 851858 * 2
def baseEnd_851858 : Nat := 291608402251888890238255

theorem tailTrace_851858 : CollatzResearch.WordTrace tailWord_851858 prefixEnd_851858 291608402251888890238255 := by
  unfold tailWord_851858
  simp only [CollatzResearch.WordTrace]
  refine ⟨7767453436967856652199057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20713209165247617739197485 7767453436967856652199057)
  ·
    refine ⟨5825590077725892489149293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7767453436967856652199057 5825590077725892489149293)
    ·
      refine ⟨2184596279147209683430985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5825590077725892489149293 2184596279147209683430985)
      ·
        refine ⟨1638447209360407262573239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2184596279147209683430985 1638447209360407262573239)
        ·
          refine ⟨2457670814040610893859859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1638447209360407262573239 2457670814040610893859859)
          ·
            refine ⟨3686506221060916340789789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2457670814040610893859859 3686506221060916340789789)
            ·
              refine ⟨1382439832897843627796171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3686506221060916340789789 1382439832897843627796171)
              ·
                refine ⟨2073659749346765441694257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1382439832897843627796171 2073659749346765441694257)
                ·
                  refine ⟨1555244812010074081270693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2073659749346765441694257 1555244812010074081270693)
                  ·
                    refine ⟨291608402251888890238255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1555244812010074081270693 291608402251888890238255)
                    ·
                      rfl

theorem cell22_851858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_851858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851858 prefixEnd_851858 := by exact prefixLift 851858
  have htrace : WordTrace (prefixWord ++ tailWord_851858) baseStart_851858 baseEnd_851858 := by
    simpa [prefixWord, tailWord_851858, baseEnd_851858] using wordTrace_append hprefix tailTrace_851858
  have hstable : (prefixWord ++ tailWord_851858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851858).length < 2 ^ (prefixWord ++ tailWord_851858).sum := by decide
  have hdescent : baseEnd_851858 < baseStart_851858 := by decide
  rcases family_descends (prefixWord ++ tailWord_851858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851978 : List Nat := [3, 1, 2, 2, 4, 1, 1, 2, 1, 5]
def baseStart_851978 : Nat := 118140960795 + 851978 * 2 ^ 59
def prefixEnd_851978 : Nat := 4983230072969 + 3 ^ 40 * 851978 * 2
def baseEnd_851978 : Nat := 291649480704248577237887

theorem tailTrace_851978 : CollatzResearch.WordTrace tailWord_851978 prefixEnd_851978 291649480704248577237887 := by
  unfold tailWord_851978
  simp only [CollatzResearch.WordTrace]
  refine ⟨7768547626859171775791147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20716127004957791402109725 7768547626859171775791147)
  ·
    refine ⟨11652821440288757663686721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7768547626859171775791147 11652821440288757663686721)
    ·
      refine ⟨8739616080216568247765041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11652821440288757663686721 8739616080216568247765041)
      ·
        refine ⟨6554712060162426185823781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8739616080216568247765041 6554712060162426185823781)
        ·
          refine ⟨1229008511280454909841959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6554712060162426185823781 1229008511280454909841959)
          ·
            refine ⟨1843512766920682364762939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229008511280454909841959 1843512766920682364762939)
            ·
              refine ⟨2765269150381023547144409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1843512766920682364762939 2765269150381023547144409)
              ·
                refine ⟨2073951862785767660358307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2765269150381023547144409 2073951862785767660358307)
                ·
                  refine ⟨3110927794178651490537461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2073951862785767660358307 3110927794178651490537461)
                  ·
                    refine ⟨291649480704248577237887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3110927794178651490537461 291649480704248577237887)
                    ·
                      rfl

theorem cell22_851978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_851978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851978 prefixEnd_851978 := by exact prefixLift 851978
  have htrace : WordTrace (prefixWord ++ tailWord_851978) baseStart_851978 baseEnd_851978 := by
    simpa [prefixWord, tailWord_851978, baseEnd_851978] using wordTrace_append hprefix tailTrace_851978
  have hstable : (prefixWord ++ tailWord_851978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851978).length < 2 ^ (prefixWord ++ tailWord_851978).sum := by decide
  have hdescent : baseEnd_851978 < baseStart_851978 := by decide
  rcases family_descends (prefixWord ++ tailWord_851978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851991 : List Nat := [1, 1, 3, 5, 2, 10]
def baseStart_851991 : Nat := 118140960795 + 851991 * 2 ^ 59
def prefixEnd_851991 : Nat := 4983230072969 + 3 ^ 40 * 851991 * 2
def baseEnd_851991 : Nat := 3600665813208899711887

theorem tailTrace_851991 : CollatzResearch.WordTrace tailWord_851991 prefixEnd_851991 3600665813208899711887 := by
  unfold tailWord_851991
  simp only [CollatzResearch.WordTrace]
  refine ⟨31074664656389590323387827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20716443104259726882258551 31074664656389590323387827)
  ·
    refine ⟨46611996984584385485081741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31074664656389590323387827 46611996984584385485081741)
    ·
      refine ⟨17479498869219144556905653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46611996984584385485081741 17479498869219144556905653)
      ·
        refine ⟨1638703018989294802209905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17479498869219144556905653 1638703018989294802209905)
        ·
          refine ⟨1229027264241971101657429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1638703018989294802209905 1229027264241971101657429)
          ·
            refine ⟨3600665813208899711887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1229027264241971101657429 3600665813208899711887)
            ·
              rfl

theorem cell22_851991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 10].length) (baseStart_851991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851991 prefixEnd_851991 := by exact prefixLift 851991
  have htrace : WordTrace (prefixWord ++ tailWord_851991) baseStart_851991 baseEnd_851991 := by
    simpa [prefixWord, tailWord_851991, baseEnd_851991] using wordTrace_append hprefix tailTrace_851991
  have hstable : (prefixWord ++ tailWord_851991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851991).length < 2 ^ (prefixWord ++ tailWord_851991).sum := by decide
  have hdescent : baseEnd_851991 < baseStart_851991 := by decide
  rcases family_descends (prefixWord ++ tailWord_851991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851997 : List Nat := [1, 4, 2, 2, 2, 3, 2, 2, 4]
def baseStart_851997 : Nat := 118140960795 + 851997 * 2 ^ 59
def prefixEnd_851997 : Nat := 4983230072969 + 3 ^ 40 * 851997 * 2
def baseEnd_851997 : Nat := 97218661597512953670943

theorem tailTrace_851997 : CollatzResearch.WordTrace tailWord_851997 prefixEnd_851997 97218661597512953670943 := by
  unfold tailWord_851997
  simp only [CollatzResearch.WordTrace]
  refine ⟨31074883494367853348106245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20716588996245235565404163 31074883494367853348106245)
  ·
    refine ⟨5826540655193972502769921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31074883494367853348106245 5826540655193972502769921)
    ·
      refine ⟨4369905491395479377077441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5826540655193972502769921 4369905491395479377077441)
      ·
        refine ⟨3277429118546609532808081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4369905491395479377077441 3277429118546609532808081)
        ·
          refine ⟨2458071838909957149606061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3277429118546609532808081 2458071838909957149606061)
          ·
            refine ⟨921776939591233931102273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2458071838909957149606061 921776939591233931102273)
            ·
              refine ⟨691332704693425448326705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 921776939591233931102273 691332704693425448326705)
              ·
                refine ⟨518499528520069086245029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 691332704693425448326705 518499528520069086245029)
                ·
                  refine ⟨97218661597512953670943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 518499528520069086245029 97218661597512953670943)
                  ·
                    rfl

theorem cell22_851997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_851997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_851997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_851997 prefixEnd_851997 := by exact prefixLift 851997
  have htrace : WordTrace (prefixWord ++ tailWord_851997) baseStart_851997 baseEnd_851997 := by
    simpa [prefixWord, tailWord_851997, baseEnd_851997] using wordTrace_append hprefix tailTrace_851997
  have hstable : (prefixWord ++ tailWord_851997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851997).length < 2 ^ (prefixWord ++ tailWord_851997).sum := by decide
  have hdescent : baseEnd_851997 < baseStart_851997 := by decide
  rcases family_descends (prefixWord ++ tailWord_851997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852053 : List Nat := [1, 3, 2, 2, 1, 3, 3, 2, 5]
def baseStart_852053 : Nat := 118140960795 + 852053 * 2 ^ 59
def prefixEnd_852053 : Nat := 4983230072969 + 3 ^ 40 * 852053 * 2
def baseEnd_852053 : Nat := 97225051578991127204219

theorem tailTrace_852053 : CollatzResearch.WordTrace tailWord_852053 prefixEnd_852053 97225051578991127204219 := by
  unfold tailWord_852053
  simp only [CollatzResearch.WordTrace]
  refine ⟨31076925982164974912144813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20717950654776649941429875 31076925982164974912144813)
  ·
    refine ⟨11653847243311865592054305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31076925982164974912144813 11653847243311865592054305)
    ·
      refine ⟨8740385432483899194040729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11653847243311865592054305 8740385432483899194040729)
      ·
        refine ⟨6555289074362924395530547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8740385432483899194040729 6555289074362924395530547)
        ·
          refine ⟨9832933611544386593295821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6555289074362924395530547 9832933611544386593295821)
          ·
            refine ⟨3687350104329144972485933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9832933611544386593295821 3687350104329144972485933)
            ·
              refine ⟨1382756289123429364682225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3687350104329144972485933 1382756289123429364682225)
              ·
                refine ⟨1037067216842572023511669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1382756289123429364682225 1037067216842572023511669)
                ·
                  refine ⟨97225051578991127204219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1037067216842572023511669 97225051578991127204219)
                  ·
                    rfl

theorem cell22_852053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_852053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852053 prefixEnd_852053 := by exact prefixLift 852053
  have htrace : WordTrace (prefixWord ++ tailWord_852053) baseStart_852053 baseEnd_852053 := by
    simpa [prefixWord, tailWord_852053, baseEnd_852053] using wordTrace_append hprefix tailTrace_852053
  have hstable : (prefixWord ++ tailWord_852053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852053).length < 2 ^ (prefixWord ++ tailWord_852053).sum := by decide
  have hdescent : baseEnd_852053 < baseStart_852053 := by decide
  rcases family_descends (prefixWord ++ tailWord_852053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852081 : List Nat := [1, 2, 2, 2, 1, 1, 3, 4, 6]
def baseStart_852081 : Nat := 118140960795 + 852081 * 2 ^ 59
def prefixEnd_852081 : Nat := 4983230072969 + 3 ^ 40 * 852081 * 2
def baseEnd_852081 : Nat := 97228246569730213970857

theorem tailTrace_852081 : CollatzResearch.WordTrace tailWord_852081 prefixEnd_852081 97228246569730213970857 := by
  unfold tailWord_852081
  simp only [CollatzResearch.WordTrace]
  refine ⟨31077947226063535694164097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20718631484042357129442731 31077947226063535694164097)
  ·
    refine ⟨23308460419547651770623073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31077947226063535694164097 23308460419547651770623073)
    ·
      refine ⟨17481345314660738827967305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23308460419547651770623073 17481345314660738827967305)
      ·
        refine ⟨13111008985995554120975479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17481345314660738827967305 13111008985995554120975479)
        ·
          refine ⟨19666513478993331181463219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13111008985995554120975479 19666513478993331181463219)
          ·
            refine ⟨29499770218489996772194829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19666513478993331181463219 29499770218489996772194829)
            ·
              refine ⟨11062413831933748789573061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29499770218489996772194829 11062413831933748789573061)
              ·
                refine ⟨2074202593487577898044949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11062413831933748789573061 2074202593487577898044949)
                ·
                  refine ⟨97228246569730213970857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2074202593487577898044949 97228246569730213970857)
                  ·
                    rfl

theorem cell22_852081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 6].length) (baseStart_852081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852081 prefixEnd_852081 := by exact prefixLift 852081
  have htrace : WordTrace (prefixWord ++ tailWord_852081) baseStart_852081 baseEnd_852081 := by
    simpa [prefixWord, tailWord_852081, baseEnd_852081] using wordTrace_append hprefix tailTrace_852081
  have hstable : (prefixWord ++ tailWord_852081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852081).length < 2 ^ (prefixWord ++ tailWord_852081).sum := by decide
  have hdescent : baseEnd_852081 < baseStart_852081 := by decide
  rcases family_descends (prefixWord ++ tailWord_852081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852096 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 3, 5]
def baseStart_852096 : Nat := 118140960795 + 852096 * 2 ^ 59
def prefixEnd_852096 : Nat := 4983230072969 + 3 ^ 40 * 852096 * 2
def baseEnd_852096 : Nat := 291689874515735602787525

theorem tailTrace_852096 : CollatzResearch.WordTrace tailWord_852096 prefixEnd_852096 291689874515735602787525 := by
  unfold tailWord_852096
  simp only [CollatzResearch.WordTrace]
  refine ⟨15539247160504596627980071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20718996214006128837306761 15539247160504596627980071)
  ·
    refine ⟨23308870740756894941970107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15539247160504596627980071 23308870740756894941970107)
    ·
      refine ⟨34963306111135342412955161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23308870740756894941970107 34963306111135342412955161)
      ·
        refine ⟨26222479583351506809716371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34963306111135342412955161 26222479583351506809716371)
        ·
          refine ⟨39333719375027260214574557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26222479583351506809716371 39333719375027260214574557)
          ·
            refine ⟨14750144765635222580465459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39333719375027260214574557 14750144765635222580465459)
            ·
              refine ⟨22125217148452833870698189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14750144765635222580465459 22125217148452833870698189)
              ·
                refine ⟨8296956430669812701511821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22125217148452833870698189 8296956430669812701511821)
                ·
                  refine ⟨3111358661501179763066933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8296956430669812701511821 3111358661501179763066933)
                  ·
                    refine ⟨291689874515735602787525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3111358661501179763066933 291689874515735602787525)
                    ·
                      rfl

theorem cell22_852096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_852096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852096 prefixEnd_852096 := by exact prefixLift 852096
  have htrace : WordTrace (prefixWord ++ tailWord_852096) baseStart_852096 baseEnd_852096 := by
    simpa [prefixWord, tailWord_852096, baseEnd_852096] using wordTrace_append hprefix tailTrace_852096
  have hstable : (prefixWord ++ tailWord_852096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852096).length < 2 ^ (prefixWord ++ tailWord_852096).sum := by decide
  have hdescent : baseEnd_852096 < baseStart_852096 := by decide
  rcases family_descends (prefixWord ++ tailWord_852096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
