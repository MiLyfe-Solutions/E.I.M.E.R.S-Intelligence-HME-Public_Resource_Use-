import V185TrunkScan23Chunk1338

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7929797 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 8]
def baseStart_7929797 : Nat := 118140960795 + 7929797 * 2 ^ 59
def prefixEnd_7929797 : Nat := 4983230072969 + 3 ^ 40 * 7929797 * 2
def baseEnd_7929797 : Nat := 4071797353581216366469033

theorem tailTrace_7929797 : CollatzResearch.WordTrace tailWord_7929797 prefixEnd_7929797 4071797353581216366469033 := by
  unfold tailWord_7929797
  simp only [CollatzResearch.WordTrace]
  refine ⟨289223457252707245351259645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192815638168471496900839763 289223457252707245351259645)
  ·
    refine ⟨108458796469765217006722367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289223457252707245351259645 108458796469765217006722367)
    ·
      refine ⟨162688194704647825510083551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108458796469765217006722367 162688194704647825510083551)
      ·
        refine ⟨244032292056971738265125327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162688194704647825510083551 244032292056971738265125327)
        ·
          refine ⟨366048438085457607397687991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244032292056971738265125327 366048438085457607397687991)
          ·
            refine ⟨549072657128186411096531987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366048438085457607397687991 549072657128186411096531987)
            ·
              refine ⟨823608985692279616644797981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549072657128186411096531987 823608985692279616644797981)
              ·
                refine ⟨308853369634604856241799243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 823608985692279616644797981 308853369634604856241799243)
                ·
                  refine ⟨463280054451907284362698865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308853369634604856241799243 463280054451907284362698865)
                  ·
                    refine ⟨347460040838930463272024149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 463280054451907284362698865 347460040838930463272024149)
                    ·
                      refine ⟨4071797353581216366469033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 347460040838930463272024149 4071797353581216366469033)
                      ·
                        rfl

theorem cell23_7929797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_7929797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929797 prefixEnd_7929797 := by exact prefixLift 7929797
  have htrace : WordTrace (prefixWord ++ tailWord_7929797) baseStart_7929797 baseEnd_7929797 := by
    simpa [prefixWord, tailWord_7929797, baseEnd_7929797] using wordTrace_append hprefix tailTrace_7929797
  have hstable : (prefixWord ++ tailWord_7929797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929797).length < 2 ^ (prefixWord ++ tailWord_7929797).sum := by decide
  have hdescent : baseEnd_7929797 < baseStart_7929797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929804 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 2, 2, 5]
def baseStart_7929804 : Nat := 118140960795 + 7929804 * 2 ^ 59
def prefixEnd_7929804 : Nat := 4983230072969 + 3 ^ 40 * 7929804 * 2
def baseEnd_7929804 : Nat := 4071800947945797839081501

theorem tailTrace_7929804 : CollatzResearch.WordTrace tailWord_7929804 prefixEnd_7929804 4071800947945797839081501 := by
  unfold tailWord_7929804
  simp only [CollatzResearch.WordTrace]
  refine ⟨144611856281840942773382233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192815808375787923697842977 144611856281840942773382233)
  ·
    refine ⟨108458892211380707080036675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144611856281840942773382233 108458892211380707080036675)
    ·
      refine ⟨162688338317071060620055013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108458892211380707080036675 162688338317071060620055013)
      ·
        refine ⟨30504063434450823866260315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162688338317071060620055013 30504063434450823866260315)
        ·
          refine ⟨45756095151676235799390473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30504063434450823866260315 45756095151676235799390473)
          ·
            refine ⟨34317071363757176849542855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45756095151676235799390473 34317071363757176849542855)
            ·
              refine ⟨51475607045635765274314283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34317071363757176849542855 51475607045635765274314283)
              ·
                refine ⟨77213410568453647911471425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51475607045635765274314283 77213410568453647911471425)
                ·
                  refine ⟨57910057926340235933603569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77213410568453647911471425 57910057926340235933603569)
                  ·
                    refine ⟨43432543444755176950202677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57910057926340235933603569 43432543444755176950202677)
                    ·
                      refine ⟨4071800947945797839081501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43432543444755176950202677 4071800947945797839081501)
                      ·
                        rfl

theorem cell23_7929804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_7929804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929804 prefixEnd_7929804 := by exact prefixLift 7929804
  have htrace : WordTrace (prefixWord ++ tailWord_7929804) baseStart_7929804 baseEnd_7929804 := by
    simpa [prefixWord, tailWord_7929804, baseEnd_7929804] using wordTrace_append hprefix tailTrace_7929804
  have hstable : (prefixWord ++ tailWord_7929804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929804).length < 2 ^ (prefixWord ++ tailWord_7929804).sum := by decide
  have hdescent : baseEnd_7929804 < baseStart_7929804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929826 : List Nat := [3, 3, 3, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_7929826 : Nat := 118140960795 + 7929826 * 2 ^ 59
def prefixEnd_7929826 : Nat := 4983230072969 + 3 ^ 40 * 7929826 * 2
def baseEnd_7929826 : Nat := 4071812244520196753006401

theorem tailTrace_7929826 : CollatzResearch.WordTrace tailWord_7929826 prefixEnd_7929826 4071812244520196753006401 := by
  unfold tailWord_7929826
  simp only [CollatzResearch.WordTrace]
  refine ⟨72306128742400545826016333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192816343313068122202710221 72306128742400545826016333)
  ·
    refine ⟨27114798278400204684756125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72306128742400545826016333 27114798278400204684756125)
    ·
      refine ⟨10168049354400076756783547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27114798278400204684756125 10168049354400076756783547)
      ·
        refine ⟨15252074031600115135175321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10168049354400076756783547 15252074031600115135175321)
        ·
          refine ⟨11439055523700086351381491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15252074031600115135175321 11439055523700086351381491)
          ·
            refine ⟨17158583285550129527072237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11439055523700086351381491 17158583285550129527072237)
            ·
              refine ⟨6434468732081298572652089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17158583285550129527072237 6434468732081298572652089)
              ·
                refine ⟨4825851549060973929489067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6434468732081298572652089 4825851549060973929489067)
                ·
                  refine ⟨7238777323591460894233601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4825851549060973929489067 7238777323591460894233601)
                  ·
                    refine ⟨5429082992693595670675201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7238777323591460894233601 5429082992693595670675201)
                    ·
                      refine ⟨4071812244520196753006401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5429082992693595670675201 4071812244520196753006401)
                      ·
                        rfl

theorem cell23_7929826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_7929826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929826 prefixEnd_7929826 := by exact prefixLift 7929826
  have htrace : WordTrace (prefixWord ++ tailWord_7929826) baseStart_7929826 baseEnd_7929826 := by
    simpa [prefixWord, tailWord_7929826, baseEnd_7929826] using wordTrace_append hprefix tailTrace_7929826
  have hstable : (prefixWord ++ tailWord_7929826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929826).length < 2 ^ (prefixWord ++ tailWord_7929826).sum := by decide
  have hdescent : baseEnd_7929826 < baseStart_7929826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929834 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_7929834 : Nat := 118140960795 + 7929834 * 2 ^ 59
def prefixEnd_7929834 : Nat := 4983230072969 + 3 ^ 40 * 7929834 * 2
def baseEnd_7929834 : Nat := 4071816352365432721706363

theorem tailTrace_7929834 : CollatzResearch.WordTrace tailWord_7929834 prefixEnd_7929834 4071816352365432721706363 := by
  unfold tailWord_7929834
  simp only [CollatzResearch.WordTrace]
  refine ⟨72306201688393300167589139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192816537835715467113571037 72306201688393300167589139)
  ·
    refine ⟨108459302532589950251383709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72306201688393300167589139 108459302532589950251383709)
    ·
      refine ⟨40672238449721231344268891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108459302532589950251383709 40672238449721231344268891)
      ·
        refine ⟨61008357674581847016403337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40672238449721231344268891 61008357674581847016403337)
        ·
          refine ⟨45756268255936385262302503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61008357674581847016403337 45756268255936385262302503)
          ·
            refine ⟨68634402383904577893453755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45756268255936385262302503 68634402383904577893453755)
            ·
              refine ⟨102951603575856866840180633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68634402383904577893453755 102951603575856866840180633)
              ·
                refine ⟨77213702681892650130135475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102951603575856866840180633 77213702681892650130135475)
                ·
                  refine ⟨115820554022838975195203213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77213702681892650130135475 115820554022838975195203213)
                  ·
                    refine ⟨43432707758564615698201205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115820554022838975195203213 43432707758564615698201205)
                    ·
                      refine ⟨4071816352365432721706363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43432707758564615698201205 4071816352365432721706363)
                      ·
                        rfl

theorem cell23_7929834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_7929834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929834 prefixEnd_7929834 := by exact prefixLift 7929834
  have htrace : WordTrace (prefixWord ++ tailWord_7929834) baseStart_7929834 baseEnd_7929834 := by
    simpa [prefixWord, tailWord_7929834, baseEnd_7929834] using wordTrace_append hprefix tailTrace_7929834
  have hstable : (prefixWord ++ tailWord_7929834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929834).length < 2 ^ (prefixWord ++ tailWord_7929834).sum := by decide
  have hdescent : baseEnd_7929834 < baseStart_7929834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929891 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 1, 7, 2]
def baseStart_7929891 : Nat := 118140960795 + 7929891 * 2 ^ 59
def prefixEnd_7929891 : Nat := 4983230072969 + 3 ^ 40 * 7929891 * 2
def baseEnd_7929891 : Nat := 4071845620762738998693601

theorem tailTrace_7929891 : CollatzResearch.WordTrace tailWord_7929891 prefixEnd_7929891 4071845620762738998693601 := by
  unfold tailWord_7929891
  simp only [CollatzResearch.WordTrace]
  refine ⟨289226885714366699405181527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192817923809577799603454351 289226885714366699405181527)
  ·
    refine ⟨433840328571550049107772291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289226885714366699405181527 433840328571550049107772291)
    ·
      refine ⟨650760492857325073661658437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433840328571550049107772291 650760492857325073661658437)
      ·
        refine ⟨122017592410748451311560957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 650760492857325073661658437 122017592410748451311560957)
        ·
          refine ⟨45756597154030669241835359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122017592410748451311560957 45756597154030669241835359)
          ·
            refine ⟨68634895731046003862753039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45756597154030669241835359 68634895731046003862753039)
            ·
              refine ⟨102952343596569005794129559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68634895731046003862753039 102952343596569005794129559)
              ·
                refine ⟨154428515394853508691194339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102952343596569005794129559 154428515394853508691194339)
                ·
                  refine ⟨231642773092280263036791509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154428515394853508691194339 231642773092280263036791509)
                  ·
                    refine ⟨5429127494350318664924801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 231642773092280263036791509 5429127494350318664924801)
                    ·
                      refine ⟨4071845620762738998693601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5429127494350318664924801 4071845620762738998693601)
                      ·
                        rfl

theorem cell23_7929891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_7929891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929891 prefixEnd_7929891 := by exact prefixLift 7929891
  have htrace : WordTrace (prefixWord ++ tailWord_7929891) baseStart_7929891 baseEnd_7929891 := by
    simpa [prefixWord, tailWord_7929891, baseEnd_7929891] using wordTrace_append hprefix tailTrace_7929891
  have hstable : (prefixWord ++ tailWord_7929891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929891).length < 2 ^ (prefixWord ++ tailWord_7929891).sum := by decide
  have hdescent : baseEnd_7929891 < baseStart_7929891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929898 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_7929898 : Nat := 118140960795 + 7929898 * 2 ^ 59
def prefixEnd_7929898 : Nat := 4983230072969 + 3 ^ 40 * 7929898 * 2
def baseEnd_7929898 : Nat := 4071849215127320471306069

theorem tailTrace_7929898 : CollatzResearch.WordTrace tailWord_7929898 prefixEnd_7929898 4071849215127320471306069 := by
  unfold tailWord_7929898
  simp only [CollatzResearch.WordTrace]
  refine ⟨72306785256335334900171587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192818094016894226400457565 72306785256335334900171587)
  ·
    refine ⟨108460177884503002350257381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72306785256335334900171587 108460177884503002350257381)
    ·
      refine ⟨20336283353344312940673259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108460177884503002350257381 20336283353344312940673259)
      ·
        refine ⟨30504425030016469411009889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20336283353344312940673259 30504425030016469411009889)
        ·
          refine ⟨22878318772512352058257417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30504425030016469411009889 22878318772512352058257417)
          ·
            refine ⟨17158739079384264043693063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22878318772512352058257417 17158739079384264043693063)
            ·
              refine ⟨25738108619076396065539595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17158739079384264043693063 25738108619076396065539595)
              ·
                refine ⟨38607162928614594098309393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25738108619076396065539595 38607162928614594098309393)
                ·
                  refine ⟨28955372196460945573732045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38607162928614594098309393 28955372196460945573732045)
                  ·
                    refine ⟨10858264573672854590149517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28955372196460945573732045 10858264573672854590149517)
                    ·
                      refine ⟨4071849215127320471306069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10858264573672854590149517 4071849215127320471306069)
                      ·
                        rfl

theorem cell23_7929898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_7929898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929898 prefixEnd_7929898 := by exact prefixLift 7929898
  have htrace : WordTrace (prefixWord ++ tailWord_7929898) baseStart_7929898 baseEnd_7929898 := by
    simpa [prefixWord, tailWord_7929898, baseEnd_7929898] using wordTrace_append hprefix tailTrace_7929898
  have hstable : (prefixWord ++ tailWord_7929898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929898).length < 2 ^ (prefixWord ++ tailWord_7929898).sum := by decide
  have hdescent : baseEnd_7929898 < baseStart_7929898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929918 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_7929918 : Nat := 118140960795 + 7929918 * 2 ^ 59
def prefixEnd_7929918 : Nat := 4983230072969 + 3 ^ 40 * 7929918 * 2
def baseEnd_7929918 : Nat := 1357286494913470131018659

theorem tailTrace_7929918 : CollatzResearch.WordTrace tailWord_7929918 prefixEnd_7929918 1357286494913470131018659 := by
  unfold tailWord_7929918
  simp only [CollatzResearch.WordTrace]
  refine ⟨36153483810658610377051801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192818580323512588677609605 36153483810658610377051801)
  ·
    refine ⟨27115112857993957782788851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36153483810658610377051801 27115112857993957782788851)
    ·
      refine ⟨40672669286990936674183277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27115112857993957782788851 40672669286990936674183277)
      ·
        refine ⟨15252250982621601252818729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40672669286990936674183277 15252250982621601252818729)
        ·
          refine ⟨11439188236966200939614047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15252250982621601252818729 11439188236966200939614047)
          ·
            refine ⟨17158782355449301409421071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11439188236966200939614047 17158782355449301409421071)
            ·
              refine ⟨25738173533173952114131607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17158782355449301409421071 25738173533173952114131607)
              ·
                refine ⟨38607260299760928171197411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25738173533173952114131607 38607260299760928171197411)
                ·
                  refine ⟨57910890449641392256796117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38607260299760928171197411 57910890449641392256796117)
                  ·
                    refine ⟨1357286494913470131018659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57910890449641392256796117 1357286494913470131018659)
                    ·
                      rfl

theorem cell23_7929918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_7929918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929918 prefixEnd_7929918 := by exact prefixLift 7929918
  have htrace : WordTrace (prefixWord ++ tailWord_7929918) baseStart_7929918 baseEnd_7929918 := by
    simpa [prefixWord, tailWord_7929918, baseEnd_7929918] using wordTrace_append hprefix tailTrace_7929918
  have hstable : (prefixWord ++ tailWord_7929918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929918).length < 2 ^ (prefixWord ++ tailWord_7929918).sum := by decide
  have hdescent : baseEnd_7929918 < baseStart_7929918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7929948 : List Nat := [2, 2, 4, 1, 1, 2, 1, 3, 3, 4]
def baseStart_7929948 : Nat := 118140960795 + 7929948 * 2 ^ 59
def prefixEnd_7929948 : Nat := 4983230072969 + 3 ^ 40 * 7929948 * 2
def baseEnd_7929948 : Nat := 1357291629720015091893613

theorem tailTrace_7929948 : CollatzResearch.WordTrace tailWord_7929948 prefixEnd_7929948 1357291629720015091893613 := by
  unfold tailWord_7929948
  simp only [CollatzResearch.WordTrace]
  refine ⟨144614482337580099070003249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192819309783440132093337665 144614482337580099070003249)
  ·
    refine ⟨108460861753185074302502437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144614482337580099070003249 108460861753185074302502437)
    ·
      refine ⟨20336411578722201431719207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108460861753185074302502437 20336411578722201431719207)
      ·
        refine ⟨30504617368083302147578811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20336411578722201431719207 30504617368083302147578811)
        ·
          refine ⟨45756926052124953221368217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30504617368083302147578811 45756926052124953221368217)
          ·
            refine ⟨34317694539093714916026163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45756926052124953221368217 34317694539093714916026163)
            ·
              refine ⟨51476541808640572374039245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34317694539093714916026163 51476541808640572374039245)
              ·
                refine ⟨19303703178240214640264717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51476541808640572374039245 19303703178240214640264717)
                ·
                  refine ⟨7238888691840080490099269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19303703178240214640264717 7238888691840080490099269)
                  ·
                    refine ⟨1357291629720015091893613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7238888691840080490099269 1357291629720015091893613)
                    ·
                      rfl

theorem cell23_7929948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_7929948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7929948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7929948 prefixEnd_7929948 := by exact prefixLift 7929948
  have htrace : WordTrace (prefixWord ++ tailWord_7929948) baseStart_7929948 baseEnd_7929948 := by
    simpa [prefixWord, tailWord_7929948, baseEnd_7929948] using wordTrace_append hprefix tailTrace_7929948
  have hstable : (prefixWord ++ tailWord_7929948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7929948).length < 2 ^ (prefixWord ++ tailWord_7929948).sum := by decide
  have hdescent : baseEnd_7929948 < baseStart_7929948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7929948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930021 : List Nat := [1, 3, 1, 2, 1, 3, 2, 3, 1, 6]
def baseStart_7930021 : Nat := 118140960795 + 7930021 * 2 ^ 59
def prefixEnd_7930021 : Nat := 4983230072969 + 3 ^ 40 * 7930021 * 2
def baseEnd_7930021 : Nat := 1357304124415941163356001

theorem tailTrace_7930021 : CollatzResearch.WordTrace tailWord_7930021 prefixEnd_7930021 1357304124415941163356001 := by
  unfold tailWord_7930021
  simp only [CollatzResearch.WordTrace]
  refine ⟨289231627203895731607413917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192821084802597154404942611 289231627203895731607413917)
  ·
    refine ⟨108461860201460899352780219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289231627203895731607413917 108461860201460899352780219)
    ·
      refine ⟨162692790302191349029170329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108461860201460899352780219 162692790302191349029170329)
      ·
        refine ⟨122019592726643511771877747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162692790302191349029170329 122019592726643511771877747)
        ·
          refine ⟨183029389089965267657816621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122019592726643511771877747 183029389089965267657816621)
          ·
            refine ⟨68636020908736975371681233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183029389089965267657816621 68636020908736975371681233)
            ·
              refine ⟨51477015681552731528760925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68636020908736975371681233 51477015681552731528760925)
              ·
                refine ⟨19303880880582274323285347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51477015681552731528760925 19303880880582274323285347)
                ·
                  refine ⟨28955821320873411484928021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19303880880582274323285347 28955821320873411484928021)
                  ·
                    refine ⟨1357304124415941163356001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28955821320873411484928021 1357304124415941163356001)
                    ·
                      rfl

theorem cell23_7930021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_7930021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930021 prefixEnd_7930021 := by exact prefixLift 7930021
  have htrace : WordTrace (prefixWord ++ tailWord_7930021) baseStart_7930021 baseEnd_7930021 := by
    simpa [prefixWord, tailWord_7930021, baseEnd_7930021] using wordTrace_append hprefix tailTrace_7930021
  have hstable : (prefixWord ++ tailWord_7930021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930021).length < 2 ^ (prefixWord ++ tailWord_7930021).sum := by decide
  have hdescent : baseEnd_7930021 < baseStart_7930021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930048 : List Nat := [2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 5]
def baseStart_7930048 : Nat := 118140960795 + 7930048 * 2 ^ 59
def prefixEnd_7930048 : Nat := 4983230072969 + 3 ^ 40 * 7930048 * 2
def baseEnd_7930048 : Nat := 4071926237225494884430379

theorem tailTrace_7930048 : CollatzResearch.WordTrace tailWord_7930048 prefixEnd_7930048 4071926237225494884430379 := by
  unfold tailWord_7930048
  simp only [CollatzResearch.WordTrace]
  refine ⟨144616305987398957609323399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192821741316531943479097865 144616305987398957609323399)
  ·
    refine ⟨216924458981098436413985099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144616305987398957609323399 216924458981098436413985099)
    ·
      refine ⟨325386688471647654620977649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216924458981098436413985099 325386688471647654620977649)
      ·
        refine ⟨244040016353735740965733237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325386688471647654620977649 244040016353735740965733237)
        ·
          refine ⟨22878751533162725715537491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 244040016353735740965733237 22878751533162725715537491)
          ·
            refine ⟨34318127299744088573306237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22878751533162725715537491 34318127299744088573306237)
            ·
              refine ⟨12869297737404033214989839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34318127299744088573306237 12869297737404033214989839)
              ·
                refine ⟨19303946606106049822484759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12869297737404033214989839 19303946606106049822484759)
                ·
                  refine ⟨28955919909159074733727139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19303946606106049822484759 28955919909159074733727139)
                  ·
                    refine ⟨43433879863738612100590709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28955919909159074733727139 43433879863738612100590709)
                    ·
                      refine ⟨4071926237225494884430379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43433879863738612100590709 4071926237225494884430379)
                      ·
                        rfl

theorem cell23_7930048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_7930048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930048 prefixEnd_7930048 := by exact prefixLift 7930048
  have htrace : WordTrace (prefixWord ++ tailWord_7930048) baseStart_7930048 baseEnd_7930048 := by
    simpa [prefixWord, tailWord_7930048, baseEnd_7930048] using wordTrace_append hprefix tailTrace_7930048
  have hstable : (prefixWord ++ tailWord_7930048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930048).length < 2 ^ (prefixWord ++ tailWord_7930048).sum := by decide
  have hdescent : baseEnd_7930048 < baseStart_7930048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930081 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 2, 7]
def baseStart_7930081 : Nat := 118140960795 + 7930081 * 2 ^ 59
def prefixEnd_7930081 : Nat := 4983230072969 + 3 ^ 40 * 7930081 * 2
def baseEnd_7930081 : Nat := 1357314394029031085105909

theorem tailTrace_7930081 : CollatzResearch.WordTrace tailWord_7930081 prefixEnd_7930081 1357314394029031085105909 := by
  unfold tailWord_7930081
  simp only [CollatzResearch.WordTrace]
  refine ⟨289233815583678361854598097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192822543722452241236398731 289233815583678361854598097)
  ·
    refine ⟨216925361687758771390948573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289233815583678361854598097 216925361687758771390948573)
    ·
      refine ⟨81347010632909539271605715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216925361687758771390948573 81347010632909539271605715)
      ·
        refine ⟨122020515949364308907408573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81347010632909539271605715 122020515949364308907408573)
        ·
          refine ⟨45757693481011615840278215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122020515949364308907408573 45757693481011615840278215)
          ·
            refine ⟨68636540221517423760417323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45757693481011615840278215 68636540221517423760417323)
            ·
              refine ⟨102954810332276135640625985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68636540221517423760417323 102954810332276135640625985)
              ·
                refine ⟨77216107749207101730469489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102954810332276135640625985 77216107749207101730469489)
                ·
                  refine ⟨57912080811905326297852117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77216107749207101730469489 57912080811905326297852117)
                  ·
                    refine ⟨1357314394029031085105909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57912080811905326297852117 1357314394029031085105909)
                    ·
                      rfl

theorem cell23_7930081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_7930081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930081 prefixEnd_7930081 := by exact prefixLift 7930081
  have htrace : WordTrace (prefixWord ++ tailWord_7930081) baseStart_7930081 baseEnd_7930081 := by
    simpa [prefixWord, tailWord_7930081, baseEnd_7930081] using wordTrace_append hprefix tailTrace_7930081
  have hstable : (prefixWord ++ tailWord_7930081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930081).length < 2 ^ (prefixWord ++ tailWord_7930081).sum := by decide
  have hdescent : baseEnd_7930081 < baseStart_7930081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930091 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 5]
def baseStart_7930091 : Nat := 118140960795 + 7930091 * 2 ^ 59
def prefixEnd_7930091 : Nat := 4983230072969 + 3 ^ 40 * 7930091 * 2
def baseEnd_7930091 : Nat := 4071948316893638216192681

theorem tailTrace_7930091 : CollatzResearch.WordTrace tailWord_7930091 prefixEnd_7930091 4071948316893638216192681 := by
  unfold tailWord_7930091
  simp only [CollatzResearch.WordTrace]
  refine ⟨289234180313642133562462127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192822786875761422374974751 289234180313642133562462127)
  ·
    refine ⟨433851270470463200343693191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289234180313642133562462127 433851270470463200343693191)
    ·
      refine ⟨650776905705694800515539787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433851270470463200343693191 650776905705694800515539787)
      ·
        refine ⟨976165358558542200773309681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650776905705694800515539787 976165358558542200773309681)
        ·
          refine ⟨732124018918906650579982261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 976165358558542200773309681 732124018918906650579982261)
          ·
            refine ⟨68636626773647498491873337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 732124018918906650579982261 68636626773647498491873337)
            ·
              refine ⟨51477470080235623868905003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68636626773647498491873337 51477470080235623868905003)
              ·
                refine ⟨77216205120353435803357505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51477470080235623868905003 77216205120353435803357505)
                ·
                  refine ⟨57912153840265076852518129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77216205120353435803357505 57912153840265076852518129)
                  ·
                    refine ⟨43434115380198807639388597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57912153840265076852518129 43434115380198807639388597)
                    ·
                      refine ⟨4071948316893638216192681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43434115380198807639388597 4071948316893638216192681)
                      ·
                        rfl

theorem cell23_7930091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 5].length) (baseStart_7930091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930091 prefixEnd_7930091 := by exact prefixLift 7930091
  have htrace : WordTrace (prefixWord ++ tailWord_7930091) baseStart_7930091 baseEnd_7930091 := by
    simpa [prefixWord, tailWord_7930091, baseEnd_7930091] using wordTrace_append hprefix tailTrace_7930091
  have hstable : (prefixWord ++ tailWord_7930091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930091).length < 2 ^ (prefixWord ++ tailWord_7930091).sum := by decide
  have hdescent : baseEnd_7930091 < baseStart_7930091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930111 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 4, 6]
def baseStart_7930111 : Nat := 118140960795 + 7930111 * 2 ^ 59
def prefixEnd_7930111 : Nat := 4983230072969 + 3 ^ 40 * 7930111 * 2
def baseEnd_7930111 : Nat := 1357319528835576045980863

theorem tailTrace_7930111 : CollatzResearch.WordTrace tailWord_7930111 prefixEnd_7930111 1357319528835576045980863 := by
  unfold tailWord_7930111
  simp only [CollatzResearch.WordTrace]
  refine ⟨289234909773569676978190187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192823273182379784652126791 289234909773569676978190187)
  ·
    refine ⟨433852364660354515467285281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289234909773569676978190187 433852364660354515467285281)
    ·
      refine ⟨325389273495265886600463961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433852364660354515467285281 325389273495265886600463961)
      ·
        refine ⟨244041955121449414950347971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325389273495265886600463961 244041955121449414950347971)
        ·
          refine ⟨366062932682174122425521957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244041955121449414950347971 366062932682174122425521957)
          ·
            refine ⟨68636799877907647954785367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 366062932682174122425521957 68636799877907647954785367)
            ·
              refine ⟨102955199816861471932178051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68636799877907647954785367 102955199816861471932178051)
              ·
                refine ⟨154432799725292207898267077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102955199816861471932178051 154432799725292207898267077)
                ·
                  refine ⟨28956149948492288980925077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154432799725292207898267077 28956149948492288980925077)
                  ·
                    refine ⟨1357319528835576045980863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28956149948492288980925077 1357319528835576045980863)
                    ·
                      rfl

theorem cell23_7930111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 6].length) (baseStart_7930111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930111 prefixEnd_7930111 := by exact prefixLift 7930111
  have htrace : WordTrace (prefixWord ++ tailWord_7930111) baseStart_7930111 baseEnd_7930111 := by
    simpa [prefixWord, tailWord_7930111, baseEnd_7930111] using wordTrace_append hprefix tailTrace_7930111
  have hstable : (prefixWord ++ tailWord_7930111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930111).length < 2 ^ (prefixWord ++ tailWord_7930111).sum := by decide
  have hdescent : baseEnd_7930111 < baseStart_7930111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930168 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 4, 3, 3]
def baseStart_7930168 : Nat := 118140960795 + 7930168 * 2 ^ 59
def prefixEnd_7930168 : Nat := 4983230072969 + 3 ^ 40 * 7930168 * 2
def baseEnd_7930168 : Nat := 4071987854904034414929827

theorem tailTrace_7930168 : CollatzResearch.WordTrace tailWord_7930168 prefixEnd_7930168 4071987854904034414929827 := by
  unfold tailWord_7930168
  simp only [CollatzResearch.WordTrace]
  refine ⟨144618494367181587856507579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192824659156242117142010105 144618494367181587856507579)
  ·
    refine ⟨216927741550772381784761369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144618494367181587856507579 216927741550772381784761369)
    ·
      refine ⟨162695806163079286338571027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216927741550772381784761369 162695806163079286338571027)
      ·
        refine ⟨244043709244618929507856541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162695806163079286338571027 244043709244618929507856541)
        ·
          refine ⟨91516390966732098565446203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244043709244618929507856541 91516390966732098565446203)
          ·
            refine ⟨137274586450098147848169305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91516390966732098565446203 137274586450098147848169305)
            ·
              refine ⟨102955939837573610886126979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137274586450098147848169305 102955939837573610886126979)
              ·
                refine ⟨154433909756360416329190469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102955939837573610886126979 154433909756360416329190469)
                ·
                  refine ⟨28956358079317578061723213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154433909756360416329190469 28956358079317578061723213)
                  ·
                    refine ⟨10858634279744091773146205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28956358079317578061723213 10858634279744091773146205)
                    ·
                      refine ⟨4071987854904034414929827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10858634279744091773146205 4071987854904034414929827)
                      ·
                        rfl

theorem cell23_7930168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_7930168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930168 prefixEnd_7930168 := by exact prefixLift 7930168
  have htrace : WordTrace (prefixWord ++ tailWord_7930168) baseStart_7930168 baseEnd_7930168 := by
    simpa [prefixWord, tailWord_7930168, baseEnd_7930168] using wordTrace_append hprefix tailTrace_7930168
  have hstable : (prefixWord ++ tailWord_7930168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930168).length < 2 ^ (prefixWord ++ tailWord_7930168).sum := by decide
  have hdescent : baseEnd_7930168 < baseStart_7930168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930188 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 4, 5]
def baseStart_7930188 : Nat := 118140960795 + 7930188 * 2 ^ 59
def prefixEnd_7930188 : Nat := 4983230072969 + 3 ^ 40 * 7930188 * 2
def baseEnd_7930188 : Nat := 1357332708172374778893245

theorem tailTrace_7930188 : CollatzResearch.WordTrace tailWord_7930188 prefixEnd_7930188 1357332708172374778893245 := by
  unfold tailWord_7930188
  simp only [CollatzResearch.WordTrace]
  refine ⟨144618859097145359564371609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192825145462860479419162145 144618859097145359564371609)
  ·
    refine ⟨108464144322859019673278707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144618859097145359564371609 108464144322859019673278707)
    ·
      refine ⟨162696216484288529509918061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108464144322859019673278707 162696216484288529509918061)
      ·
        refine ⟨61011081181608198566219273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162696216484288529509918061 61011081181608198566219273)
        ·
          refine ⟨45758310886206148924664455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61011081181608198566219273 45758310886206148924664455)
          ·
            refine ⟨68637466329309223386996683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45758310886206148924664455 68637466329309223386996683)
            ·
              refine ⟨102956199493963835080495025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68637466329309223386996683 102956199493963835080495025)
              ·
                refine ⟨77217149620472876310371269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102956199493963835080495025 77217149620472876310371269)
                ·
                  refine ⟨14478215553838664308194613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77217149620472876310371269 14478215553838664308194613)
                  ·
                    refine ⟨1357332708172374778893245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14478215553838664308194613 1357332708172374778893245)
                    ·
                      rfl

theorem cell23_7930188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_7930188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930188 prefixEnd_7930188 := by exact prefixLift 7930188
  have htrace : WordTrace (prefixWord ++ tailWord_7930188) baseStart_7930188 baseEnd_7930188 := by
    simpa [prefixWord, tailWord_7930188, baseEnd_7930188] using wordTrace_append hprefix tailTrace_7930188
  have hstable : (prefixWord ++ tailWord_7930188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930188).length < 2 ^ (prefixWord ++ tailWord_7930188).sum := by decide
  have hdescent : baseEnd_7930188 < baseStart_7930188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930225 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 2, 4, 2]
def baseStart_7930225 : Nat := 118140960795 + 7930225 * 2 ^ 59
def prefixEnd_7930225 : Nat := 4983230072969 + 3 ^ 40 * 7930225 * 2
def baseEnd_7930225 : Nat := 4072017123301340691917065

theorem tailTrace_7930225 : CollatzResearch.WordTrace tailWord_7930225 prefixEnd_7930225 4072017123301340691917065 := by
  unfold tailWord_7930225
  simp only [CollatzResearch.WordTrace]
  refine ⟨289239067695156674447840129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192826045130104449631893419 289239067695156674447840129)
  ·
    refine ⟨216929300771367505835880097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289239067695156674447840129 216929300771367505835880097)
    ·
      refine ⟨162696975578525629376910073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216929300771367505835880097 162696975578525629376910073)
      ·
        refine ⟨122022731683894222032682555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162696975578525629376910073 122022731683894222032682555)
        ·
          refine ⟨183034097525841333049023833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122022731683894222032682555 183034097525841333049023833)
          ·
            refine ⟨137275573144380999786767875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183034097525841333049023833 137275573144380999786767875)
            ·
              refine ⟨205913359716571499680151813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137275573144380999786767875 205913359716571499680151813)
              ·
                refine ⟨38608754946857156190028465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205913359716571499680151813 38608754946857156190028465)
                ·
                  refine ⟨28956566210142867142521349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38608754946857156190028465 28956566210142867142521349)
                  ·
                    refine ⟨5429356164401787589222753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28956566210142867142521349 5429356164401787589222753)
                    ·
                      refine ⟨4072017123301340691917065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5429356164401787589222753 4072017123301340691917065)
                      ·
                        rfl

theorem cell23_7930225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_7930225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930225 prefixEnd_7930225 := by exact prefixLift 7930225
  have htrace : WordTrace (prefixWord ++ tailWord_7930225) baseStart_7930225 baseEnd_7930225 := by
    simpa [prefixWord, tailWord_7930225, baseEnd_7930225] using wordTrace_append hprefix tailTrace_7930225
  have hstable : (prefixWord ++ tailWord_7930225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930225).length < 2 ^ (prefixWord ++ tailWord_7930225).sum := by decide
  have hdescent : baseEnd_7930225 < baseStart_7930225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930302 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2]
def baseStart_7930302 : Nat := 118140960795 + 7930302 * 2 ^ 59
def prefixEnd_7930302 : Nat := 4983230072969 + 3 ^ 40 * 7930302 * 2
def baseEnd_7930302 : Nat := 4072056661311736890654211

theorem tailTrace_7930302 : CollatzResearch.WordTrace tailWord_7930302 prefixEnd_7930302 4072056661311736890654211 := by
  unfold tailWord_7930302
  simp only [CollatzResearch.WordTrace]
  refine ⟨36155234514484714574799145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192827917410585144398928773 36155234514484714574799145)
  ·
    refine ⟨27116425885863535931099359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36155234514484714574799145 27116425885863535931099359)
    ·
      refine ⟨40674638828795303896649039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27116425885863535931099359 40674638828795303896649039)
      ·
        refine ⟨61011958243192955844973559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40674638828795303896649039 61011958243192955844973559)
        ·
          refine ⟨91517937364789433767460339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61011958243192955844973559 91517937364789433767460339)
          ·
            refine ⟨137276906047184150651190509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91517937364789433767460339 137276906047184150651190509)
            ·
              refine ⟨51478839767694056494196441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137276906047184150651190509 51478839767694056494196441)
              ·
                refine ⟨38609129825770542370647331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51478839767694056494196441 38609129825770542370647331)
                ·
                  refine ⟨57913694738655813555970997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38609129825770542370647331 57913694738655813555970997)
                  ·
                    refine ⟨5429408881748982520872281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57913694738655813555970997 5429408881748982520872281)
                    ·
                      refine ⟨4072056661311736890654211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5429408881748982520872281 4072056661311736890654211)
                      ·
                        rfl

theorem cell23_7930302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_7930302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930302 prefixEnd_7930302 := by exact prefixLift 7930302
  have htrace : WordTrace (prefixWord ++ tailWord_7930302) baseStart_7930302 baseEnd_7930302 := by
    simpa [prefixWord, tailWord_7930302, baseEnd_7930302] using wordTrace_append hprefix tailTrace_7930302
  have hstable : (prefixWord ++ tailWord_7930302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930302).length < 2 ^ (prefixWord ++ tailWord_7930302).sum := by decide
  have hdescent : baseEnd_7930302 < baseStart_7930302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930312 : List Nat := [2, 1, 3, 1, 3, 3, 2, 2, 1, 5]
def baseStart_7930312 : Nat := 118140960795 + 7930312 * 2 ^ 59
def prefixEnd_7930312 : Nat := 4983230072969 + 3 ^ 40 * 7930312 * 2
def baseEnd_7930312 : Nat := 1357353932039427283843055

theorem tailTrace_7930312 : CollatzResearch.WordTrace tailWord_7930312 prefixEnd_7930312 1357353932039427283843055 := by
  unfold tailWord_7930312
  simp only [CollatzResearch.WordTrace]
  refine ⟨144621120422920744153128595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192828160563894325537504793 144621120422920744153128595)
  ·
    refine ⟨216931680634381116229692893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144621120422920744153128595 216931680634381116229692893)
    ·
      refine ⟨81349380237892918586134835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216931680634381116229692893 81349380237892918586134835)
      ·
        refine ⟨122024070356839377879202253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81349380237892918586134835 122024070356839377879202253)
        ·
          refine ⟨45759026383814766704700845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122024070356839377879202253 45759026383814766704700845)
          ·
            refine ⟨17159634893930537514262817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45759026383814766704700845 17159634893930537514262817)
            ·
              refine ⟨12869726170447903135697113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17159634893930537514262817 12869726170447903135697113)
              ·
                refine ⟨9652294627835927351772835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12869726170447903135697113 9652294627835927351772835)
                ·
                  refine ⟨14478441941753891027659253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9652294627835927351772835 14478441941753891027659253)
                  ·
                    refine ⟨1357353932039427283843055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14478441941753891027659253 1357353932039427283843055)
                    ·
                      rfl

theorem cell23_7930312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_7930312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930312 prefixEnd_7930312 := by exact prefixLift 7930312
  have htrace : WordTrace (prefixWord ++ tailWord_7930312) baseStart_7930312 baseEnd_7930312 := by
    simpa [prefixWord, tailWord_7930312, baseEnd_7930312] using wordTrace_append hprefix tailTrace_7930312
  have hstable : (prefixWord ++ tailWord_7930312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930312).length < 2 ^ (prefixWord ++ tailWord_7930312).sum := by decide
  have hdescent : baseEnd_7930312 < baseStart_7930312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930315 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 1, 8, 2]
def baseStart_7930315 : Nat := 118140960795 + 7930315 * 2 ^ 59
def prefixEnd_7930315 : Nat := 4983230072969 + 3 ^ 40 * 7930315 * 2
def baseEnd_7930315 : Nat := 4072063336560245339791651

theorem tailTrace_7930315 : CollatzResearch.WordTrace tailWord_7930315 prefixEnd_7930315 4072063336560245339791651 := by
  unfold tailWord_7930315
  simp only [CollatzResearch.WordTrace]
  refine ⟨289242350264830619818616399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192828233509887079879077599 289242350264830619818616399)
  ·
    refine ⟨433863525397245929727924599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289242350264830619818616399 433863525397245929727924599)
    ·
      refine ⟨650795288095868894591886899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433863525397245929727924599 650795288095868894591886899)
      ·
        refine ⟨976192932143803341887830349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650795288095868894591886899 976192932143803341887830349)
        ·
          refine ⟨366072349553926253207936381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 976192932143803341887830349 366072349553926253207936381)
          ·
            refine ⟨137277131082722344952976143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366072349553926253207936381 137277131082722344952976143)
            ·
              refine ⟨205915696624083517429464215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137277131082722344952976143 205915696624083517429464215)
              ·
                refine ⟨308873544936125276144196323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205915696624083517429464215 308873544936125276144196323)
                ·
                  refine ⟨463310317404187914216294485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308873544936125276144196323 463310317404187914216294485)
                  ·
                    refine ⟨5429417782080327119722201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 463310317404187914216294485 5429417782080327119722201)
                    ·
                      refine ⟨4072063336560245339791651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5429417782080327119722201 4072063336560245339791651)
                      ·
                        rfl

theorem cell23_7930315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 8, 2].length) (baseStart_7930315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930315 prefixEnd_7930315 := by exact prefixLift 7930315
  have htrace : WordTrace (prefixWord ++ tailWord_7930315) baseStart_7930315 baseEnd_7930315 := by
    simpa [prefixWord, tailWord_7930315, baseEnd_7930315] using wordTrace_append hprefix tailTrace_7930315
  have hstable : (prefixWord ++ tailWord_7930315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930315).length < 2 ^ (prefixWord ++ tailWord_7930315).sum := by decide
  have hdescent : baseEnd_7930315 < baseStart_7930315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930335 : List Nat := [1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 5]
def baseStart_7930335 : Nat := 118140960795 + 7930335 * 2 ^ 59
def prefixEnd_7930335 : Nat := 4983230072969 + 3 ^ 40 * 7930335 * 2
def baseEnd_7930335 : Nat := 4072073606173335261541559

theorem tailTrace_7930335 : CollatzResearch.WordTrace tailWord_7930335 prefixEnd_7930335 4072073606173335261541559 := by
  unfold tailWord_7930335
  simp only [CollatzResearch.WordTrace]
  refine ⟨289243079724758163234344459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192828719816505442156229639 289243079724758163234344459)
  ·
    refine ⟨433864619587137244851516689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289243079724758163234344459 433864619587137244851516689)
    ·
      refine ⟨325398464690352933638637517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433864619587137244851516689 325398464690352933638637517)
      ·
        refine ⟨122024424258882350114489069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325398464690352933638637517 122024424258882350114489069)
        ·
          refine ⟨45759159097080881292933401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122024424258882350114489069 45759159097080881292933401)
          ·
            refine ⟨34319369322810660969700051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45759159097080881292933401 34319369322810660969700051)
            ·
              refine ⟨51479053984215991454550077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34319369322810660969700051 51479053984215991454550077)
              ·
                refine ⟨19304645244080996795456279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51479053984215991454550077 19304645244080996795456279)
                ·
                  refine ⟨28956967866121495193184419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19304645244080996795456279 28956967866121495193184419)
                  ·
                    refine ⟨43435451799182242789776629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28956967866121495193184419 43435451799182242789776629)
                    ·
                      refine ⟨4072073606173335261541559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43435451799182242789776629 4072073606173335261541559)
                      ·
                        rfl

theorem cell23_7930335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_7930335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930335 prefixEnd_7930335 := by exact prefixLift 7930335
  have htrace : WordTrace (prefixWord ++ tailWord_7930335) baseStart_7930335 baseEnd_7930335 := by
    simpa [prefixWord, tailWord_7930335, baseEnd_7930335] using wordTrace_append hprefix tailTrace_7930335
  have hstable : (prefixWord ++ tailWord_7930335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930335).length < 2 ^ (prefixWord ++ tailWord_7930335).sum := by decide
  have hdescent : baseEnd_7930335 < baseStart_7930335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930369 : List Nat := [1, 2, 4, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_7930369 : Nat := 118140960795 + 7930369 * 2 ^ 59
def prefixEnd_7930369 : Nat := 4983230072969 + 3 ^ 40 * 7930369 * 2
def baseEnd_7930369 : Nat := 4072091064515588128516403

theorem tailTrace_7930369 : CollatzResearch.WordTrace tailWord_7930369 prefixEnd_7930369 4072091064515588128516403 := by
  unfold tailWord_7930369
  simp only [CollatzResearch.WordTrace]
  refine ⟨289244319806634987041082161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192829546537756658027388107 289244319806634987041082161)
  ·
    refine ⟨216933239854976240280811621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289244319806634987041082161 216933239854976240280811621)
    ·
      refine ⟨40674982472808045052652179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216933239854976240280811621 40674982472808045052652179)
      ·
        refine ⟨61012473709212067578978269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40674982472808045052652179 61012473709212067578978269)
        ·
          refine ⟨22879677640954525342116851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61012473709212067578978269 22879677640954525342116851)
          ·
            refine ⟨34319516461431788013175277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22879677640954525342116851 34319516461431788013175277)
            ·
              refine ⟨12869818673036920504940729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34319516461431788013175277 12869818673036920504940729)
              ·
                refine ⟨9652364004777690378705547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12869818673036920504940729 9652364004777690378705547)
                ·
                  refine ⟨14478546007166535568058321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9652364004777690378705547 14478546007166535568058321)
                  ·
                    refine ⟨10858909505374901676043741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14478546007166535568058321 10858909505374901676043741)
                    ·
                      refine ⟨4072091064515588128516403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10858909505374901676043741 4072091064515588128516403)
                      ·
                        rfl

theorem cell23_7930369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_7930369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930369 prefixEnd_7930369 := by exact prefixLift 7930369
  have htrace : WordTrace (prefixWord ++ tailWord_7930369) baseStart_7930369 baseEnd_7930369 := by
    simpa [prefixWord, tailWord_7930369, baseEnd_7930369] using wordTrace_append hprefix tailTrace_7930369
  have hstable : (prefixWord ++ tailWord_7930369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930369).length < 2 ^ (prefixWord ++ tailWord_7930369).sum := by decide
  have hdescent : baseEnd_7930369 < baseStart_7930369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930382 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3]
def baseStart_7930382 : Nat := 118140960795 + 7930382 * 2 ^ 59
def prefixEnd_7930382 : Nat := 4983230072969 + 3 ^ 40 * 7930382 * 2
def baseEnd_7930382 : Nat := 4072097739764096577653843

theorem tailTrace_7930382 : CollatzResearch.WordTrace tailWord_7930382 prefixEnd_7930382 4072097739764096577653843 := by
  unfold tailWord_7930382
  simp only [CollatzResearch.WordTrace]
  refine ⟨36155599244448486282663175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192829862637058593507536933 36155599244448486282663175)
  ·
    refine ⟨54233398866672729423994763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36155599244448486282663175 54233398866672729423994763)
    ·
      refine ⟨81350098300009094135992145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54233398866672729423994763 81350098300009094135992145)
      ·
        refine ⟨61012573725006820601994109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81350098300009094135992145 61012573725006820601994109)
        ·
          refine ⟨22879715146877557725747791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61012573725006820601994109 22879715146877557725747791)
          ·
            refine ⟨34319572720316336588621687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22879715146877557725747791 34319572720316336588621687)
            ·
              refine ⟨51479359080474504882932531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34319572720316336588621687 51479359080474504882932531)
              ·
                refine ⟨77219038620711757324398797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51479359080474504882932531 77219038620711757324398797)
                ·
                  refine ⟨28957139482766908996649549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77219038620711757324398797 28957139482766908996649549)
                  ·
                    refine ⟨10858927306037590873743581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28957139482766908996649549 10858927306037590873743581)
                    ·
                      refine ⟨4072097739764096577653843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10858927306037590873743581 4072097739764096577653843)
                      ·
                        rfl

theorem cell23_7930382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_7930382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930382 prefixEnd_7930382 := by exact prefixLift 7930382
  have htrace : WordTrace (prefixWord ++ tailWord_7930382) baseStart_7930382 baseEnd_7930382 := by
    simpa [prefixWord, tailWord_7930382, baseEnd_7930382] using wordTrace_append hprefix tailTrace_7930382
  have hstable : (prefixWord ++ tailWord_7930382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930382).length < 2 ^ (prefixWord ++ tailWord_7930382).sum := by decide
  have hdescent : baseEnd_7930382 < baseStart_7930382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930405 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 2, 3, 4]
def baseStart_7930405 : Nat := 118140960795 + 7930405 * 2 ^ 59
def prefixEnd_7930405 : Nat := 4983230072969 + 3 ^ 40 * 7930405 * 2
def baseEnd_7930405 : Nat := 4072109549819149987666237

theorem tailTrace_7930405 : CollatzResearch.WordTrace tailWord_7930405 prefixEnd_7930405 4072109549819149987666237 := by
  unfold tailWord_7930405
  simp only [CollatzResearch.WordTrace]
  refine ⟨289245632834504565189392669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192830421889669710126261779 289245632834504565189392669)
  ·
    refine ⟨108467112312939211946022251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289245632834504565189392669 108467112312939211946022251)
    ·
      refine ⟨162700668469408817919033377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108467112312939211946022251 162700668469408817919033377)
      ·
        refine ⟨122025501352056613439275033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162700668469408817919033377 122025501352056613439275033)
        ·
          refine ⟨91519126014042460079456275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122025501352056613439275033 91519126014042460079456275)
          ·
            refine ⟨137278689021063690119184413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91519126014042460079456275 137278689021063690119184413)
            ·
              refine ⟨51479508382898883794694155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137278689021063690119184413 51479508382898883794694155)
              ·
                refine ⟨77219262574348325692041233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51479508382898883794694155 77219262574348325692041233)
                ·
                  refine ⟨57914446930761244269030925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77219262574348325692041233 57914446930761244269030925)
                  ·
                    refine ⟨21717917599035466600886597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57914446930761244269030925 21717917599035466600886597)
                    ·
                      refine ⟨4072109549819149987666237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21717917599035466600886597 4072109549819149987666237)
                      ·
                        rfl

theorem cell23_7930405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_7930405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930405 prefixEnd_7930405 := by exact prefixLift 7930405
  have htrace : WordTrace (prefixWord ++ tailWord_7930405) baseStart_7930405 baseEnd_7930405 := by
    simpa [prefixWord, tailWord_7930405, baseEnd_7930405] using wordTrace_append hprefix tailTrace_7930405
  have hstable : (prefixWord ++ tailWord_7930405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930405).length < 2 ^ (prefixWord ++ tailWord_7930405).sum := by decide
  have hdescent : baseEnd_7930405 < baseStart_7930405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930413 : List Nat := [1, 5, 4, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_7930413 : Nat := 118140960795 + 7930413 * 2 ^ 59
def prefixEnd_7930413 : Nat := 4983230072969 + 3 ^ 40 * 7930413 * 2
def baseEnd_7930413 : Nat := 4072113657664385956366201

theorem tailTrace_7930413 : CollatzResearch.WordTrace tailWord_7930413 prefixEnd_7930413 4072113657664385956366201 := by
  unfold tailWord_7930413
  simp only [CollatzResearch.WordTrace]
  refine ⟨289245924618475582555683893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192830616412317055037122595 289245924618475582555683893)
  ·
    refine ⟨27116805432982085864595365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289245924618475582555683893 27116805432982085864595365)
    ·
      refine ⟨5084401018684141099611631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27116805432982085864595365 5084401018684141099611631)
      ·
        refine ⟨7626601528026211649417447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5084401018684141099611631 7626601528026211649417447)
        ·
          refine ⟨11439902292039317474126171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7626601528026211649417447 11439902292039317474126171)
          ·
            refine ⟨17159853438058976211189257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11439902292039317474126171 17159853438058976211189257)
            ·
              refine ⟨12869890078544232158391943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17159853438058976211189257 12869890078544232158391943)
              ·
                refine ⟨19304835117816348237587915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12869890078544232158391943 19304835117816348237587915)
                ·
                  refine ⟨28957252676724522356381873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19304835117816348237587915 28957252676724522356381873)
                  ·
                    refine ⟨21717939507543391767286405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28957252676724522356381873 21717939507543391767286405)
                    ·
                      refine ⟨4072113657664385956366201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21717939507543391767286405 4072113657664385956366201)
                      ·
                        rfl

theorem cell23_7930413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_7930413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930413 prefixEnd_7930413 := by exact prefixLift 7930413
  have htrace : WordTrace (prefixWord ++ tailWord_7930413) baseStart_7930413 baseEnd_7930413 := by
    simpa [prefixWord, tailWord_7930413, baseEnd_7930413] using wordTrace_append hprefix tailTrace_7930413
  have hstable : (prefixWord ++ tailWord_7930413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930413).length < 2 ^ (prefixWord ++ tailWord_7930413).sum := by decide
  have hdescent : baseEnd_7930413 < baseStart_7930413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930439 : List Nat := [1, 1, 4, 1, 4, 1, 2, 2, 1, 4, 2]
def baseStart_7930439 : Nat := 118140960795 + 7930439 * 2 ^ 59
def prefixEnd_7930439 : Nat := 4983230072969 + 3 ^ 40 * 7930439 * 2
def baseEnd_7930439 : Nat := 4072127008161402854641081

theorem tailTrace_7930439 : CollatzResearch.WordTrace tailWord_7930439 prefixEnd_7930439 4072127008161402854641081 := by
  unfold tailWord_7930439
  simp only [CollatzResearch.WordTrace]
  refine ⟨289246872916381388996130371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192831248610920925997420247 289246872916381388996130371)
  ·
    refine ⟨433870309374572083494195557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289246872916381388996130371 433870309374572083494195557)
    ·
      refine ⟨81350683007732265655161667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 433870309374572083494195557 81350683007732265655161667)
      ·
        refine ⟨122026024511598398482742501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81350683007732265655161667 122026024511598398482742501)
        ·
          refine ⟨22879879595924699715514219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122026024511598398482742501 22879879595924699715514219)
          ·
            refine ⟨34319819393887049573271329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22879879595924699715514219 34319819393887049573271329)
            ·
              refine ⟨25739864545415287179953497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34319819393887049573271329 25739864545415287179953497)
              ·
                refine ⟨19304898409061465384965123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25739864545415287179953497 19304898409061465384965123)
                ·
                  refine ⟨28957347613592198077447685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19304898409061465384965123 28957347613592198077447685)
                  ·
                    refine ⟨5429502677548537139521441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28957347613592198077447685 5429502677548537139521441)
                    ·
                      refine ⟨4072127008161402854641081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5429502677548537139521441 4072127008161402854641081)
                      ·
                        rfl

theorem cell23_7930439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_7930439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930439 prefixEnd_7930439 := by exact prefixLift 7930439
  have htrace : WordTrace (prefixWord ++ tailWord_7930439) baseStart_7930439 baseEnd_7930439 := by
    simpa [prefixWord, tailWord_7930439, baseEnd_7930439] using wordTrace_append hprefix tailTrace_7930439
  have hstable : (prefixWord ++ tailWord_7930439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930439).length < 2 ^ (prefixWord ++ tailWord_7930439).sum := by decide
  have hdescent : baseEnd_7930439 < baseStart_7930439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930452 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_7930452 : Nat := 118140960795 + 7930452 * 2 ^ 59
def prefixEnd_7930452 : Nat := 4983230072969 + 3 ^ 40 * 7930452 * 2
def baseEnd_7930452 : Nat := 4072133683409911303778521

theorem tailTrace_7930452 : CollatzResearch.WordTrace tailWord_7930452 prefixEnd_7930452 4072133683409911303778521 := by
  unfold tailWord_7930452
  simp only [CollatzResearch.WordTrace]
  refine ⟨144623673532667146108176805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192831564710222861477569073 144623673532667146108176805)
  ·
    refine ⟨27116938787375089895283151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144623673532667146108176805 27116938787375089895283151)
    ·
      refine ⟨40675408181062634842924727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27116938787375089895283151 40675408181062634842924727)
      ·
        refine ⟨61013112271593952264387091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40675408181062634842924727 61013112271593952264387091)
        ·
          refine ⟨91519668407390928396580637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61013112271593952264387091 91519668407390928396580637)
          ·
            refine ⟨34319875652771598148717739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91519668407390928396580637 34319875652771598148717739)
            ·
              refine ⟨51479813479157397223076609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34319875652771598148717739 51479813479157397223076609)
              ·
                refine ⟨38609860109368047917307457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51479813479157397223076609 38609860109368047917307457)
                ·
                  refine ⟨28957395082026035937980593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38609860109368047917307457 28957395082026035937980593)
                  ·
                    refine ⟨21718046311519526953485445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28957395082026035937980593 21718046311519526953485445)
                    ·
                      refine ⟨4072133683409911303778521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21718046311519526953485445 4072133683409911303778521)
                      ·
                        rfl

theorem cell23_7930452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_7930452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930452 prefixEnd_7930452 := by exact prefixLift 7930452
  have htrace : WordTrace (prefixWord ++ tailWord_7930452) baseStart_7930452 baseEnd_7930452 := by
    simpa [prefixWord, tailWord_7930452, baseEnd_7930452] using wordTrace_append hprefix tailTrace_7930452
  have hstable : (prefixWord ++ tailWord_7930452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930452).length < 2 ^ (prefixWord ++ tailWord_7930452).sum := by decide
  have hdescent : baseEnd_7930452 < baseStart_7930452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930456 : List Nat := [2, 1, 2, 2, 1, 2, 5, 2, 2, 2, 2]
def baseStart_7930456 : Nat := 118140960795 + 7930456 * 2 ^ 59
def prefixEnd_7930456 : Nat := 4983230072969 + 3 ^ 40 * 7930456 * 2
def baseEnd_7930456 : Nat := 4072135737332529288128503

theorem tailTrace_7930456 : CollatzResearch.WordTrace tailWord_7930456 prefixEnd_7930456 4072135737332529288128503 := by
  unfold tailWord_7930456
  simp only [CollatzResearch.WordTrace]
  refine ⟨144623746478659900449749611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192831661971546533932999481 144623746478659900449749611)
  ·
    refine ⟨216935619717989850674624417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144623746478659900449749611 216935619717989850674624417)
    ·
      refine ⟨162701714788492388005968313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216935619717989850674624417 162701714788492388005968313)
      ·
        refine ⟨122026286091369291004476235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162701714788492388005968313 122026286091369291004476235)
        ·
          refine ⟨183039429137053936506714353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122026286091369291004476235 183039429137053936506714353)
          ·
            refine ⟨137279571852790452380035765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183039429137053936506714353 137279571852790452380035765)
            ·
              refine ⟨12869959861199104910628353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137279571852790452380035765 12869959861199104910628353)
              ·
                refine ⟨9652469895899328682971265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12869959861199104910628353 9652469895899328682971265)
                ·
                  refine ⟨7239352421924496512228449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9652469895899328682971265 7239352421924496512228449)
                  ·
                    refine ⟨5429514316443372384171337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7239352421924496512228449 5429514316443372384171337)
                    ·
                      refine ⟨4072135737332529288128503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5429514316443372384171337 4072135737332529288128503)
                      ·
                        rfl

theorem cell23_7930456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_7930456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930456 prefixEnd_7930456 := by exact prefixLift 7930456
  have htrace : WordTrace (prefixWord ++ tailWord_7930456) baseStart_7930456 baseEnd_7930456 := by
    simpa [prefixWord, tailWord_7930456, baseEnd_7930456] using wordTrace_append hprefix tailTrace_7930456
  have hstable : (prefixWord ++ tailWord_7930456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930456).length < 2 ^ (prefixWord ++ tailWord_7930456).sum := by decide
  have hdescent : baseEnd_7930456 < baseStart_7930456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930475 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 6, 5]
def baseStart_7930475 : Nat := 118140960795 + 7930475 * 2 ^ 59
def prefixEnd_7930475 : Nat := 4983230072969 + 3 ^ 40 * 7930475 * 2
def baseEnd_7930475 : Nat := 1357381831154988237930305

theorem tailTrace_7930475 : CollatzResearch.WordTrace tailWord_7930475 prefixEnd_7930475 1357381831154988237930305 := by
  unfold tailWord_7930475
  simp only [CollatzResearch.WordTrace]
  refine ⟨289248185944250967144440879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192832123962833978096293919 289248185944250967144440879)
  ·
    refine ⟨433872278916376450716661319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289248185944250967144440879 433872278916376450716661319)
    ·
      refine ⟨650808418374564676074991979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433872278916376450716661319 650808418374564676074991979)
      ·
        refine ⟨976212627561847014112487969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650808418374564676074991979 976212627561847014112487969)
        ·
          refine ⟨732159470671385260584365977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 976212627561847014112487969 732159470671385260584365977)
          ·
            refine ⟨549119603003538945438274483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 732159470671385260584365977 549119603003538945438274483)
            ·
              refine ⟨823679404505308418157411725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549119603003538945438274483 823679404505308418157411725)
              ·
                refine ⟨308879776689490656809029397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 823679404505308418157411725 308879776689490656809029397)
                ·
                  refine ⟨14478739532319874537923253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 308879776689490656809029397 14478739532319874537923253)
                  ·
                    refine ⟨1357381831154988237930305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14478739532319874537923253 1357381831154988237930305)
                    ·
                      rfl

theorem cell23_7930475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 5].length) (baseStart_7930475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930475 prefixEnd_7930475 := by exact prefixLift 7930475
  have htrace : WordTrace (prefixWord ++ tailWord_7930475) baseStart_7930475 baseEnd_7930475 := by
    simpa [prefixWord, tailWord_7930475, baseEnd_7930475] using wordTrace_append hprefix tailTrace_7930475
  have hstable : (prefixWord ++ tailWord_7930475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930475).length < 2 ^ (prefixWord ++ tailWord_7930475).sum := by decide
  have hdescent : baseEnd_7930475 < baseStart_7930475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930515 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 5]
def baseStart_7930515 : Nat := 118140960795 + 7930515 * 2 ^ 59
def prefixEnd_7930515 : Nat := 4983230072969 + 3 ^ 40 * 7930515 * 2
def baseEnd_7930515 : Nat := 4072166032691144557290731

theorem tailTrace_7930515 : CollatzResearch.WordTrace tailWord_7930515 prefixEnd_7930515 4072166032691144557290731 := by
  unfold tailWord_7930515
  simp only [CollatzResearch.WordTrace]
  refine ⟨289249644864106053975896999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192833096576070702650597999 289249644864106053975896999)
  ·
    refine ⟨433874467296159080963845499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289249644864106053975896999 433874467296159080963845499)
    ·
      refine ⟨650811700944238621445768249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433874467296159080963845499 650811700944238621445768249)
      ·
        refine ⟨488108775708178966084326187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650811700944238621445768249 488108775708178966084326187)
        ·
          refine ⟨732163163562268449126489281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488108775708178966084326187 732163163562268449126489281)
          ·
            refine ⟨549122372671701336844866961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 732163163562268449126489281 549122372671701336844866961)
            ·
              refine ⟨411841779503776002633650221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549122372671701336844866961 411841779503776002633650221)
              ·
                refine ⟨154440667313916000987618833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 411841779503776002633650221 154440667313916000987618833)
                ·
                  refine ⟨115830500485437000740714125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154440667313916000987618833 115830500485437000740714125)
                  ·
                    refine ⟨43436437682038875277767797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115830500485437000740714125 43436437682038875277767797)
                    ·
                      refine ⟨4072166032691144557290731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43436437682038875277767797 4072166032691144557290731)
                      ·
                        rfl

theorem cell23_7930515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_7930515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930515 prefixEnd_7930515 := by exact prefixLift 7930515
  have htrace : WordTrace (prefixWord ++ tailWord_7930515) baseStart_7930515 baseEnd_7930515 := by
    simpa [prefixWord, tailWord_7930515, baseEnd_7930515] using wordTrace_append hprefix tailTrace_7930515
  have hstable : (prefixWord ++ tailWord_7930515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930515).length < 2 ^ (prefixWord ++ tailWord_7930515).sum := by decide
  have hdescent : baseEnd_7930515 < baseStart_7930515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930555 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 8]
def baseStart_7930555 : Nat := 118140960795 + 7930555 * 2 ^ 59
def prefixEnd_7930555 : Nat := 4983230072969 + 3 ^ 40 * 7930555 * 2
def baseEnd_7930555 : Nat := 4072186571917324400790547

theorem tailTrace_7930555 : CollatzResearch.WordTrace tailWord_7930555 prefixEnd_7930555 4072186571917324400790547 := by
  unfold tailWord_7930555
  simp only [CollatzResearch.WordTrace]
  refine ⟨289251103783961140807353119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192834069189307427204902079 289251103783961140807353119)
  ·
    refine ⟨433876655675941711211029679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289251103783961140807353119 433876655675941711211029679)
    ·
      refine ⟨650814983513912566816544519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433876655675941711211029679 650814983513912566816544519)
      ·
        refine ⟨976222475270868850224816779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650814983513912566816544519 976222475270868850224816779)
        ·
          refine ⟨1464333712906303275337225169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976222475270868850224816779 1464333712906303275337225169)
          ·
            refine ⟨1098250284679727456502918877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1464333712906303275337225169 1098250284679727456502918877)
            ·
              refine ⟨411843856754897796188594579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1098250284679727456502918877 411843856754897796188594579)
              ·
                refine ⟨617765785132346694282891869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411843856754897796188594579 617765785132346694282891869)
                ·
                  refine ⟨231662169424630010356084451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 617765785132346694282891869 231662169424630010356084451)
                  ·
                    refine ⟨347493254136945015534126677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 231662169424630010356084451 347493254136945015534126677)
                    ·
                      refine ⟨4072186571917324400790547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 347493254136945015534126677 4072186571917324400790547)
                      ·
                        rfl

theorem cell23_7930555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 8].length) (baseStart_7930555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930555 prefixEnd_7930555 := by exact prefixLift 7930555
  have htrace : WordTrace (prefixWord ++ tailWord_7930555) baseStart_7930555 baseEnd_7930555 := by
    simpa [prefixWord, tailWord_7930555, baseEnd_7930555] using wordTrace_append hprefix tailTrace_7930555
  have hstable : (prefixWord ++ tailWord_7930555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930555).length < 2 ^ (prefixWord ++ tailWord_7930555).sum := by decide
  have hdescent : baseEnd_7930555 < baseStart_7930555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930556 : List Nat := [2, 2, 2, 3, 1, 1, 2, 5, 1, 4]
def baseStart_7930556 : Nat := 118140960795 + 7930556 * 2 ^ 59
def prefixEnd_7930556 : Nat := 4983230072969 + 3 ^ 40 * 7930556 * 2
def baseEnd_7930556 : Nat := 1357395695132659632292681

theorem tailTrace_7930556 : CollatzResearch.WordTrace tailWord_7930556 prefixEnd_7930556 1357395695132659632292681 := by
  unfold tailWord_7930556
  simp only [CollatzResearch.WordTrace]
  refine ⟨144625570128478758989069761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192834093504638345318759681 144625570128478758989069761)
  ·
    refine ⟨108469177596359069241802321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144625570128478758989069761 108469177596359069241802321)
    ·
      refine ⟨81351883197269301931351741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108469177596359069241802321 81351883197269301931351741)
      ·
        refine ⟨30506956198975988224256903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81351883197269301931351741 30506956198975988224256903)
        ·
          refine ⟨45760434298463982336385355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30506956198975988224256903 45760434298463982336385355)
          ·
            refine ⟨68640651447695973504578033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45760434298463982336385355 68640651447695973504578033)
            ·
              refine ⟨51480488585771980128433525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68640651447695973504578033 51480488585771980128433525)
              ·
                refine ⟨4826295804916123137040643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51480488585771980128433525 4826295804916123137040643)
                ·
                  refine ⟨7239443707374184705560965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4826295804916123137040643 7239443707374184705560965)
                  ·
                    refine ⟨1357395695132659632292681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7239443707374184705560965 1357395695132659632292681)
                    ·
                      rfl

theorem cell23_7930556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_7930556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930556 prefixEnd_7930556 := by exact prefixLift 7930556
  have htrace : WordTrace (prefixWord ++ tailWord_7930556) baseStart_7930556 baseEnd_7930556 := by
    simpa [prefixWord, tailWord_7930556, baseEnd_7930556] using wordTrace_append hprefix tailTrace_7930556
  have hstable : (prefixWord ++ tailWord_7930556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930556).length < 2 ^ (prefixWord ++ tailWord_7930556).sum := by decide
  have hdescent : baseEnd_7930556 < baseStart_7930556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930596 : List Nat := [2, 3, 1, 1, 1, 5, 1, 2, 3, 1, 3]
def baseStart_7930596 : Nat := 118140960795 + 7930596 * 2 ^ 59
def prefixEnd_7930596 : Nat := 4983230072969 + 3 ^ 40 * 7930596 * 2
def baseEnd_7930596 : Nat := 4072207624624158740377859

theorem tailTrace_7930596 : CollatzResearch.WordTrace tailWord_7930596 prefixEnd_7930596 4072207624624158740377859 := by
  unfold tailWord_7930596
  simp only [CollatzResearch.WordTrace]
  refine ⟨144626299588406302404797821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192835066117875069873063761 144626299588406302404797821)
  ·
    refine ⟨54234862345652363401799183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144626299588406302404797821 54234862345652363401799183)
    ·
      refine ⟨81352293518478545102698775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54234862345652363401799183 81352293518478545102698775)
      ·
        refine ⟨122028440277717817654048163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81352293518478545102698775 122028440277717817654048163)
        ·
          refine ⟨183042660416576726481072245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122028440277717817654048163 183042660416576726481072245)
          ·
            refine ⟨17160249414054068107600523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183042660416576726481072245 17160249414054068107600523)
            ·
              refine ⟨25740374121081102161400785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17160249414054068107600523 25740374121081102161400785)
              ·
                refine ⟨19305280590810826621050589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25740374121081102161400785 19305280590810826621050589)
                ·
                  refine ⟨7239480221554059982893971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19305280590810826621050589 7239480221554059982893971)
                  ·
                    refine ⟨10859220332331089974340957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7239480221554059982893971 10859220332331089974340957)
                    ·
                      refine ⟨4072207624624158740377859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10859220332331089974340957 4072207624624158740377859)
                      ·
                        rfl

theorem cell23_7930596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_7930596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930596 prefixEnd_7930596 := by exact prefixLift 7930596
  have htrace : WordTrace (prefixWord ++ tailWord_7930596) baseStart_7930596 baseEnd_7930596 := by
    simpa [prefixWord, tailWord_7930596, baseEnd_7930596] using wordTrace_append hprefix tailTrace_7930596
  have hstable : (prefixWord ++ tailWord_7930596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930596).length < 2 ^ (prefixWord ++ tailWord_7930596).sum := by decide
  have hdescent : baseEnd_7930596 < baseStart_7930596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930606 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 1, 5, 2]
def baseStart_7930606 : Nat := 118140960795 + 7930606 * 2 ^ 59
def prefixEnd_7930606 : Nat := 4983230072969 + 3 ^ 40 * 7930606 * 2
def baseEnd_7930606 : Nat := 4072212759430703701252813

theorem tailTrace_7930606 : CollatzResearch.WordTrace tailWord_7930606 prefixEnd_7930606 4072212759430703701252813 := by
  unfold tailWord_7930606
  simp only [CollatzResearch.WordTrace]
  refine ⟨36156620488347047064682459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192835309271184251011639781 36156620488347047064682459)
  ·
    refine ⟨54234930732520570597023689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36156620488347047064682459 54234930732520570597023689)
    ·
      refine ⟨40676198049390427947767767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54234930732520570597023689 40676198049390427947767767)
      ·
        refine ⟨61014297074085641921651651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40676198049390427947767767 61014297074085641921651651)
        ·
          refine ⟨91521445611128462882477477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61014297074085641921651651 91521445611128462882477477)
          ·
            refine ⟨17160271052086586790464527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91521445611128462882477477 17160271052086586790464527)
            ·
              refine ⟨25740406578129880185696791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17160271052086586790464527 25740406578129880185696791)
              ·
                refine ⟨38610609867194820278545187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25740406578129880185696791 38610609867194820278545187)
                ·
                  refine ⟨57915914800792230417817781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38610609867194820278545187 57915914800792230417817781)
                  ·
                    refine ⟨5429617012574271601670417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57915914800792230417817781 5429617012574271601670417)
                    ·
                      refine ⟨4072212759430703701252813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5429617012574271601670417 4072212759430703701252813)
                      ·
                        rfl

theorem cell23_7930606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_7930606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930606 prefixEnd_7930606 := by exact prefixLift 7930606
  have htrace : WordTrace (prefixWord ++ tailWord_7930606) baseStart_7930606 baseEnd_7930606 := by
    simpa [prefixWord, tailWord_7930606, baseEnd_7930606] using wordTrace_append hprefix tailTrace_7930606
  have hstable : (prefixWord ++ tailWord_7930606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930606).length < 2 ^ (prefixWord ++ tailWord_7930606).sum := by decide
  have hdescent : baseEnd_7930606 < baseStart_7930606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930656 : List Nat := [2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 3]
def baseStart_7930656 : Nat := 118140960795 + 7930656 * 2 ^ 59
def prefixEnd_7930656 : Nat := 4983230072969 + 3 ^ 40 * 7930656 * 2
def baseEnd_7930656 : Nat := 4072238433463428505627583

theorem tailTrace_7930656 : CollatzResearch.WordTrace tailWord_7930656 prefixEnd_7930656 4072238433463428505627583 := by
  unfold tailWord_7930656
  simp only [CollatzResearch.WordTrace]
  refine ⟨144627393778297617528389911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192836525037730156704519881 144627393778297617528389911)
  ·
    refine ⟨216941090667446426292584867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144627393778297617528389911 216941090667446426292584867)
    ·
      refine ⟨325411636001169639438877301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216941090667446426292584867 325411636001169639438877301)
      ·
        refine ⟨30507340875109653697394747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325411636001169639438877301 30507340875109653697394747)
        ·
          refine ⟨45761011312664480546092121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30507340875109653697394747 45761011312664480546092121)
          ·
            refine ⟨34320758484498360409569091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45761011312664480546092121 34320758484498360409569091)
            ·
              refine ⟨51481137726747540614353637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34320758484498360409569091 51481137726747540614353637)
              ·
                refine ⟨9652713323765163865191307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51481137726747540614353637 9652713323765163865191307)
                ·
                  refine ⟨14479069985647745797786961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9652713323765163865191307 14479069985647745797786961)
                  ·
                    refine ⟨10859302489235809348340221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14479069985647745797786961 10859302489235809348340221)
                    ·
                      refine ⟨4072238433463428505627583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10859302489235809348340221 4072238433463428505627583)
                      ·
                        rfl

theorem cell23_7930656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_7930656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930656 prefixEnd_7930656 := by exact prefixLift 7930656
  have htrace : WordTrace (prefixWord ++ tailWord_7930656) baseStart_7930656 baseEnd_7930656 := by
    simpa [prefixWord, tailWord_7930656, baseEnd_7930656] using wordTrace_append hprefix tailTrace_7930656
  have hstable : (prefixWord ++ tailWord_7930656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930656).length < 2 ^ (prefixWord ++ tailWord_7930656).sum := by decide
  have hdescent : baseEnd_7930656 < baseStart_7930656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930676 : List Nat := [2, 5, 1, 1, 3, 2, 9]
def baseStart_7930676 : Nat := 118140960795 + 7930676 * 2 ^ 59
def prefixEnd_7930676 : Nat := 4983230072969 + 3 ^ 40 * 7930676 * 2
def baseEnd_7930676 : Nat := 50274675346623684288611

theorem tailTrace_7930676 : CollatzResearch.WordTrace tailWord_7930676 prefixEnd_7930676 50274675346623684288611 := by
  unfold tailWord_7930676
  simp only [CollatzResearch.WordTrace]
  refine ⟨144627758508261389236253941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192837011344348518981671921 144627758508261389236253941)
  ·
    refine ⟨13558852360149505240898807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144627758508261389236253941 13558852360149505240898807)
    ·
      refine ⟨20338278540224257861348211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13558852360149505240898807 20338278540224257861348211)
      ·
        refine ⟨30507417810336386792022317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20338278540224257861348211 30507417810336386792022317)
        ·
          refine ⟨11440281678876145047008369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30507417810336386792022317 11440281678876145047008369)
          ·
            refine ⟨8580211259157108785256277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11440281678876145047008369 8580211259157108785256277)
            ·
              refine ⟨50274675346623684288611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8580211259157108785256277 50274675346623684288611)
              ·
                rfl

theorem cell23_7930676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 9].length) (baseStart_7930676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930676 prefixEnd_7930676 := by exact prefixLift 7930676
  have htrace : WordTrace (prefixWord ++ tailWord_7930676) baseStart_7930676 baseEnd_7930676 := by
    simpa [prefixWord, tailWord_7930676, baseEnd_7930676] using wordTrace_append hprefix tailTrace_7930676
  have hstable : (prefixWord ++ tailWord_7930676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930676).length < 2 ^ (prefixWord ++ tailWord_7930676).sum := by decide
  have hdescent : baseEnd_7930676 < baseStart_7930676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930687 : List Nat := [1, 1, 2, 2, 5, 2, 3, 2, 1, 2, 2]
def baseStart_7930687 : Nat := 118140960795 + 7930687 * 2 ^ 59
def prefixEnd_7930687 : Nat := 4983230072969 + 3 ^ 40 * 7930687 * 2
def baseEnd_7930687 : Nat := 4072254351363717884339941

theorem tailTrace_7930687 : CollatzResearch.WordTrace tailWord_7930687 prefixEnd_7930687 4072254351363717884339941 := by
  unfold tailWord_7930687
  simp only [CollatzResearch.WordTrace]
  refine ⟨289255918219482927351158315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192837278812988618234105543 289255918219482927351158315)
  ·
    refine ⟨433883877329224391026737473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289255918219482927351158315 433883877329224391026737473)
    ·
      refine ⟨325412907996918293270053105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433883877329224391026737473 325412907996918293270053105)
      ·
        refine ⟨244059680997688719952539829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325412907996918293270053105 244059680997688719952539829)
        ·
          refine ⟨22880595093533317495550609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 244059680997688719952539829 22880595093533317495550609)
          ·
            refine ⟨17160446320149988121662957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22880595093533317495550609 17160446320149988121662957)
            ·
              refine ⟨6435167370056245545623609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17160446320149988121662957 6435167370056245545623609)
              ·
                refine ⟨4826375527542184159217707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6435167370056245545623609 4826375527542184159217707)
                ·
                  refine ⟨7239563291313276238826561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4826375527542184159217707 7239563291313276238826561)
                  ·
                    refine ⟨5429672468484957179119921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7239563291313276238826561 5429672468484957179119921)
                    ·
                      refine ⟨4072254351363717884339941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5429672468484957179119921 4072254351363717884339941)
                      ·
                        rfl

theorem cell23_7930687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 1, 2, 2].length) (baseStart_7930687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930687 prefixEnd_7930687 := by exact prefixLift 7930687
  have htrace : WordTrace (prefixWord ++ tailWord_7930687) baseStart_7930687 baseEnd_7930687 := by
    simpa [prefixWord, tailWord_7930687, baseEnd_7930687] using wordTrace_append hprefix tailTrace_7930687
  have hstable : (prefixWord ++ tailWord_7930687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930687).length < 2 ^ (prefixWord ++ tailWord_7930687).sum := by decide
  have hdescent : baseEnd_7930687 < baseStart_7930687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930696 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 3, 3, 2]
def baseStart_7930696 : Nat := 118140960795 + 7930696 * 2 ^ 59
def prefixEnd_7930696 : Nat := 4983230072969 + 3 ^ 40 * 7930696 * 2
def baseEnd_7930696 : Nat := 4072258972689608349127399

theorem tailTrace_7930696 : CollatzResearch.WordTrace tailWord_7930696 prefixEnd_7930696 4072258972689608349127399 := by
  unfold tailWord_7930696
  simp only [CollatzResearch.WordTrace]
  refine ⟨144628123238225160944117971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192837497650966881258823961 144628123238225160944117971)
  ·
    refine ⟨216942184857337741416176957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144628123238225160944117971 216942184857337741416176957)
    ·
      refine ⟨81353319321501653031066359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216942184857337741416176957 81353319321501653031066359)
      ·
        refine ⟨122029978982252479546599539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81353319321501653031066359 122029978982252479546599539)
        ·
          refine ⟨183044968473378719319899309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122029978982252479546599539 183044968473378719319899309)
          ·
            refine ⟨68641863177517019744962241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183044968473378719319899309 68641863177517019744962241)
            ·
              refine ⟨51481397383137764808721681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68641863177517019744962241 51481397383137764808721681)
              ·
                refine ⟨38611048037353323606541261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51481397383137764808721681 38611048037353323606541261)
                ·
                  refine ⟨14479143014007496352452973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38611048037353323606541261 14479143014007496352452973)
                  ·
                    refine ⟨5429678630252811132169865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14479143014007496352452973 5429678630252811132169865)
                    ·
                      refine ⟨4072258972689608349127399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5429678630252811132169865 4072258972689608349127399)
                      ·
                        rfl

theorem cell23_7930696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_7930696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930696 prefixEnd_7930696 := by exact prefixLift 7930696
  have htrace : WordTrace (prefixWord ++ tailWord_7930696) baseStart_7930696 baseEnd_7930696 := by
    simpa [prefixWord, tailWord_7930696, baseEnd_7930696] using wordTrace_append hprefix tailTrace_7930696
  have hstable : (prefixWord ++ tailWord_7930696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930696).length < 2 ^ (prefixWord ++ tailWord_7930696).sum := by decide
  have hdescent : baseEnd_7930696 < baseStart_7930696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930713 : List Nat := [1, 2, 1, 2, 2, 4, 3, 2, 1, 3, 2]
def baseStart_7930713 : Nat := 118140960795 + 7930713 * 2 ^ 59
def prefixEnd_7930713 : Nat := 4983230072969 + 3 ^ 40 * 7930713 * 2
def baseEnd_7930713 : Nat := 4072267701860734782614821

theorem tailTrace_7930713 : CollatzResearch.WordTrace tailWord_7930713 prefixEnd_7930713 4072267701860734782614821 := by
  unfold tailWord_7930713
  simp only [CollatzResearch.WordTrace]
  refine ⟨289256866517388733791604793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192837911011592489194403195 289256866517388733791604793)
  ·
    refine ⟨216942649888041550343703595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289256866517388733791604793 216942649888041550343703595)
    ·
      refine ⟨325413974832062325515555393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216942649888041550343703595 325413974832062325515555393)
      ·
        refine ⟨244060481124046744136666545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325413974832062325515555393 244060481124046744136666545)
        ·
          refine ⟨183045360843035058102499909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244060481124046744136666545 183045360843035058102499909)
          ·
            refine ⟨34321005158069073394218733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183045360843035058102499909 34321005158069073394218733)
            ·
              refine ⟨12870376934275902522832025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34321005158069073394218733 12870376934275902522832025)
              ·
                refine ⟨9652782700706926892124019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12870376934275902522832025 9652782700706926892124019)
                ·
                  refine ⟨14479174051060390338186029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9652782700706926892124019 14479174051060390338186029)
                  ·
                    refine ⟨5429690269147646376819761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14479174051060390338186029 5429690269147646376819761)
                    ·
                      refine ⟨4072267701860734782614821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5429690269147646376819761 4072267701860734782614821)
                      ·
                        rfl

theorem cell23_7930713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 3, 2].length) (baseStart_7930713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930713 prefixEnd_7930713 := by exact prefixLift 7930713
  have htrace : WordTrace (prefixWord ++ tailWord_7930713) baseStart_7930713 baseEnd_7930713 := by
    simpa [prefixWord, tailWord_7930713, baseEnd_7930713] using wordTrace_append hprefix tailTrace_7930713
  have hstable : (prefixWord ++ tailWord_7930713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930713).length < 2 ^ (prefixWord ++ tailWord_7930713).sum := by decide
  have hdescent : baseEnd_7930713 < baseStart_7930713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930760 : List Nat := [2, 1, 3, 3, 2, 1, 2, 3, 2, 2, 2]
def baseStart_7930760 : Nat := 118140960795 + 7930760 * 2 ^ 59
def prefixEnd_7930760 : Nat := 4983230072969 + 3 ^ 40 * 7930760 * 2
def baseEnd_7930760 : Nat := 4072291835451496098727105

theorem tailTrace_7930760 : CollatzResearch.WordTrace tailWord_7930760 prefixEnd_7930760 4072291835451496098727105 := by
  unfold tailWord_7930760
  simp only [CollatzResearch.WordTrace]
  refine ⟨144629290374109230409282867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192839053832145640545710489 144629290374109230409282867)
  ·
    refine ⟨216943935561163845613924301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144629290374109230409282867 216943935561163845613924301)
    ·
      refine ⟨81353975835436442105221613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216943935561163845613924301 81353975835436442105221613)
      ·
        refine ⟨30507740938288665789458105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81353975835436442105221613 30507740938288665789458105)
        ·
          refine ⟨22880805703716499342093579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30507740938288665789458105 22880805703716499342093579)
          ·
            refine ⟨34321208555574749013140369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22880805703716499342093579 34321208555574749013140369)
            ·
              refine ⟨25740906416681061759855277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34321208555574749013140369 25740906416681061759855277)
              ·
                refine ⟨9652839906255398159945729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25740906416681061759855277 9652839906255398159945729)
                ·
                  refine ⟨7239629929691548619959297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9652839906255398159945729 7239629929691548619959297)
                  ·
                    refine ⟨5429722447268661464969473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7239629929691548619959297 5429722447268661464969473)
                    ·
                      refine ⟨4072291835451496098727105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5429722447268661464969473 4072291835451496098727105)
                      ·
                        rfl

theorem cell23_7930760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_7930760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930760 prefixEnd_7930760 := by exact prefixLift 7930760
  have htrace : WordTrace (prefixWord ++ tailWord_7930760) baseStart_7930760 baseEnd_7930760 := by
    simpa [prefixWord, tailWord_7930760, baseEnd_7930760] using wordTrace_append hprefix tailTrace_7930760
  have hstable : (prefixWord ++ tailWord_7930760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930760).length < 2 ^ (prefixWord ++ tailWord_7930760).sum := by decide
  have hdescent : baseEnd_7930760 < baseStart_7930760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930783 : List Nat := [1, 1, 2, 5, 2, 2, 2, 3, 5]
def baseStart_7930783 : Nat := 118140960795 + 7930783 * 2 ^ 59
def prefixEnd_7930783 : Nat := 4983230072969 + 3 ^ 40 * 7930783 * 2
def baseEnd_7930783 : Nat := 452478182834061056526611

theorem tailTrace_7930783 : CollatzResearch.WordTrace tailWord_7930783 prefixEnd_7930783 452478182834061056526611 := by
  unfold tailWord_7930783
  simp only [CollatzResearch.WordTrace]
  refine ⟨289259419627135135746653003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192839613084756757164435335 289259419627135135746653003)
  ·
    refine ⟨433889129440702703619979505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289259419627135135746653003 433889129440702703619979505)
    ·
      refine ⟨325416847080527027714984629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433889129440702703619979505 325416847080527027714984629)
      ·
        refine ⟨30507829413799408848279809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325416847080527027714984629 30507829413799408848279809)
        ·
          refine ⟨22880872060349556636209857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30507829413799408848279809 22880872060349556636209857)
          ·
            refine ⟨17160654045262167477157393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22880872060349556636209857 17160654045262167477157393)
            ·
              refine ⟨12870490533946625607868045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17160654045262167477157393 12870490533946625607868045)
              ·
                refine ⟨4826433950229984602950517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12870490533946625607868045 4826433950229984602950517)
                ·
                  refine ⟨452478182834061056526611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4826433950229984602950517 452478182834061056526611)
                  ·
                    rfl

theorem cell23_7930783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 5].length) (baseStart_7930783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930783 prefixEnd_7930783 := by exact prefixLift 7930783
  have htrace : WordTrace (prefixWord ++ tailWord_7930783) baseStart_7930783 baseEnd_7930783 := by
    simpa [prefixWord, tailWord_7930783, baseEnd_7930783] using wordTrace_append hprefix tailTrace_7930783
  have hstable : (prefixWord ++ tailWord_7930783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930783).length < 2 ^ (prefixWord ++ tailWord_7930783).sum := by decide
  have hdescent : baseEnd_7930783 < baseStart_7930783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930850 : List Nat := [3, 3, 3, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_7930850 : Nat := 118140960795 + 7930850 * 2 ^ 59
def prefixEnd_7930850 : Nat := 4983230072969 + 3 ^ 40 * 7930850 * 2
def baseEnd_7930850 : Nat := 4072338048710400746601691

theorem tailTrace_7930850 : CollatzResearch.WordTrace tailWord_7930850 prefixEnd_7930850 4072338048710400746601691 := by
  unfold tailWord_7930850
  simp only [CollatzResearch.WordTrace]
  refine ⟨72315465829473101547335501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192841242211928270792894669 72315465829473101547335501)
  ·
    refine ⟨27118299686052413080250813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72315465829473101547335501 27118299686052413080250813)
    ·
      refine ⟨10169362382269654905094055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27118299686052413080250813 10169362382269654905094055)
      ·
        refine ⟨15254043573404482357641083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10169362382269654905094055 15254043573404482357641083)
        ·
          refine ⟨22881065360106723536461625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15254043573404482357641083 22881065360106723536461625)
          ·
            refine ⟨17160799020080042652346219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22881065360106723536461625 17160799020080042652346219)
            ·
              refine ⟨25741198530120063978519329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17160799020080042652346219 25741198530120063978519329)
              ·
                refine ⟨19305898897590047983889497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25741198530120063978519329 19305898897590047983889497)
                ·
                  refine ⟨14479424173192535987917123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19305898897590047983889497 14479424173192535987917123)
                  ·
                    refine ⟨21719136259788803981875685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14479424173192535987917123 21719136259788803981875685)
                    ·
                      refine ⟨4072338048710400746601691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21719136259788803981875685 4072338048710400746601691)
                      ·
                        rfl

theorem cell23_7930850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_7930850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930850 prefixEnd_7930850 := by exact prefixLift 7930850
  have htrace : WordTrace (prefixWord ++ tailWord_7930850) baseStart_7930850 baseEnd_7930850 := by
    simpa [prefixWord, tailWord_7930850, baseEnd_7930850] using wordTrace_append hprefix tailTrace_7930850
  have hstable : (prefixWord ++ tailWord_7930850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930850).length < 2 ^ (prefixWord ++ tailWord_7930850).sum := by decide
  have hdescent : baseEnd_7930850 < baseStart_7930850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930940 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 5, 2, 2]
def baseStart_7930940 : Nat := 118140960795 + 7930940 * 2 ^ 59
def prefixEnd_7930940 : Nat := 4983230072969 + 3 ^ 40 * 7930940 * 2
def baseEnd_7930940 : Nat := 4072384261969305394476277

theorem tailTrace_7930940 : CollatzResearch.WordTrace tailWord_7930940 prefixEnd_7930940 4072384261969305394476277 := by
  unfold tailWord_7930940
  simp only [CollatzResearch.WordTrace]
  refine ⟨144632572943783175780059137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192843430591710901040078849 144632572943783175780059137)
  ·
    refine ⟨108474429707837381835044353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144632572943783175780059137 108474429707837381835044353)
    ·
      refine ⟨81355822280878036376283265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108474429707837381835044353 81355822280878036376283265)
      ·
        refine ⟨61016866710658527282212449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81355822280878036376283265 61016866710658527282212449)
        ·
          refine ⟨45762650032993895461659337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61016866710658527282212449 45762650032993895461659337)
          ·
            refine ⟨34321987524745421596244503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45762650032993895461659337 34321987524745421596244503)
            ·
              refine ⟨51482981287118132394366755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34321987524745421596244503 51482981287118132394366755)
              ·
                refine ⟨77224471930677198591550133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51482981287118132394366755 77224471930677198591550133)
                ·
                  refine ⟨7239794243500987367957825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77224471930677198591550133 7239794243500987367957825)
                  ·
                    refine ⟨5429845682625740525968369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7239794243500987367957825 5429845682625740525968369)
                    ·
                      refine ⟨4072384261969305394476277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5429845682625740525968369 4072384261969305394476277)
                      ·
                        rfl

theorem cell23_7930940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_7930940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930940 prefixEnd_7930940 := by exact prefixLift 7930940
  have htrace : WordTrace (prefixWord ++ tailWord_7930940) baseStart_7930940 baseEnd_7930940 := by
    simpa [prefixWord, tailWord_7930940, baseEnd_7930940] using wordTrace_append hprefix tailTrace_7930940
  have hstable : (prefixWord ++ tailWord_7930940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930940).length < 2 ^ (prefixWord ++ tailWord_7930940).sum := by decide
  have hdescent : baseEnd_7930940 < baseStart_7930940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930943 : List Nat := [1, 1, 2, 2, 3, 1, 1, 6, 1, 2, 3]
def baseStart_7930943 : Nat := 118140960795 + 7930943 * 2 ^ 59
def prefixEnd_7930943 : Nat := 4983230072969 + 3 ^ 40 * 7930943 * 2
def baseEnd_7930943 : Nat := 4072385802411268882738763

theorem tailTrace_7930943 : CollatzResearch.WordTrace tailWord_7930943 prefixEnd_7930943 4072385802411268882738763 := by
  unfold tailWord_7930943
  simp only [CollatzResearch.WordTrace]
  refine ⟨289265255306555483072477483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192843503537703655381651655 289265255306555483072477483)
  ·
    refine ⟨433897882959833224608716225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289265255306555483072477483 433897882959833224608716225)
    ·
      refine ⟨325423412219874918456537169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433897882959833224608716225 325423412219874918456537169)
      ·
        refine ⟨244067559164906188842402877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325423412219874918456537169 244067559164906188842402877)
        ·
          refine ⟨91525334686839820815901079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244067559164906188842402877 91525334686839820815901079)
          ·
            refine ⟨137288002030259731223851619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91525334686839820815901079 137288002030259731223851619)
            ·
              refine ⟨205932003045389596835777429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137288002030259731223851619 205932003045389596835777429)
              ·
                refine ⟨9653062642752637351677067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 205932003045389596835777429 9653062642752637351677067)
                ·
                  refine ⟨14479593964128956027515601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9653062642752637351677067 14479593964128956027515601)
                  ·
                    refine ⟨10859695473096717020636701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14479593964128956027515601 10859695473096717020636701)
                    ·
                      refine ⟨4072385802411268882738763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10859695473096717020636701 4072385802411268882738763)
                      ·
                        rfl

theorem cell23_7930943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 2, 3].length) (baseStart_7930943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930943 prefixEnd_7930943 := by exact prefixLift 7930943
  have htrace : WordTrace (prefixWord ++ tailWord_7930943) baseStart_7930943 baseEnd_7930943 := by
    simpa [prefixWord, tailWord_7930943, baseEnd_7930943] using wordTrace_append hprefix tailTrace_7930943
  have hstable : (prefixWord ++ tailWord_7930943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930943).length < 2 ^ (prefixWord ++ tailWord_7930943).sum := by decide
  have hdescent : baseEnd_7930943 < baseStart_7930943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930950 : List Nat := [6, 1, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_7930950 : Nat := 118140960795 + 7930950 * 2 ^ 59
def prefixEnd_7930950 : Nat := 4983230072969 + 3 ^ 40 * 7930950 * 2
def baseEnd_7930950 : Nat := 1357463132258616785117077

theorem tailTrace_7930950 : CollatzResearch.WordTrace tailWord_7930950 prefixEnd_7930950 1357463132258616785117077 := by
  unfold tailWord_7930950
  simp only [CollatzResearch.WordTrace]
  refine ⟨9039547206797816352124447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 192843673745020082178654869 9039547206797816352124447)
  ·
    refine ⟨13559320810196724528186671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9039547206797816352124447 13559320810196724528186671)
    ·
      refine ⟨20338981215295086792280007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13559320810196724528186671 20338981215295086792280007)
      ·
        refine ⟨30508471822942630188420011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20338981215295086792280007 30508471822942630188420011)
        ·
          refine ⟨45762707734413945282630017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30508471822942630188420011 45762707734413945282630017)
          ·
            refine ⟨34322030800810458961972513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45762707734413945282630017 34322030800810458961972513)
            ·
              refine ⟨25741523100607844221479385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34322030800810458961972513 25741523100607844221479385)
              ·
                refine ⟨19306142325455883166109539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25741523100607844221479385 19306142325455883166109539)
                ·
                  refine ⟨28959213488183824749164309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19306142325455883166109539 28959213488183824749164309)
                  ·
                    refine ⟨1357463132258616785117077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28959213488183824749164309 1357463132258616785117077)
                    ·
                      rfl

theorem cell23_7930950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_7930950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930950 prefixEnd_7930950 := by exact prefixLift 7930950
  have htrace : WordTrace (prefixWord ++ tailWord_7930950) baseStart_7930950 baseEnd_7930950 := by
    simpa [prefixWord, tailWord_7930950, baseEnd_7930950] using wordTrace_append hprefix tailTrace_7930950
  have hstable : (prefixWord ++ tailWord_7930950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930950).length < 2 ^ (prefixWord ++ tailWord_7930950).sum := by decide
  have hdescent : baseEnd_7930950 < baseStart_7930950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930957 : List Nat := [1, 6, 1, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_7930957 : Nat := 118140960795 + 7930957 * 2 ^ 59
def prefixEnd_7930957 : Nat := 4983230072969 + 3 ^ 40 * 7930957 * 2
def baseEnd_7930957 : Nat := 4072392991140431827963699

theorem tailTrace_7930957 : CollatzResearch.WordTrace tailWord_7930957 prefixEnd_7930957 4072392991140431827963699 := by
  unfold tailWord_7930957
  simp only [CollatzResearch.WordTrace]
  refine ⟨289265765928504763463487125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192843843952336508975658083 289265765928504763463487125)
  ·
    refine ⟨13559332777898660787350959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 289265765928504763463487125 13559332777898660787350959)
    ·
      refine ⟨20338999166847991181026439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13559332777898660787350959 20338999166847991181026439)
      ·
        refine ⟨30508498750271986771539659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20338999166847991181026439 30508498750271986771539659)
        ·
          refine ⟨45762748125407980157309489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30508498750271986771539659 45762748125407980157309489)
          ·
            refine ⟨34322061094055985117982117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45762748125407980157309489 34322061094055985117982117)
            ·
              refine ⟨6435386455135497209621647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34322061094055985117982117 6435386455135497209621647)
              ·
                refine ⟨9653079682703245814432471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6435386455135497209621647 9653079682703245814432471)
                ·
                  refine ⟨14479619524054868721648707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9653079682703245814432471 14479619524054868721648707)
                  ·
                    refine ⟨21719429286082303082473061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14479619524054868721648707 21719429286082303082473061)
                    ·
                      refine ⟨4072392991140431827963699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21719429286082303082473061 4072392991140431827963699)
                      ·
                        rfl

theorem cell23_7930957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_7930957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930957 prefixEnd_7930957 := by exact prefixLift 7930957
  have htrace : WordTrace (prefixWord ++ tailWord_7930957) baseStart_7930957 baseEnd_7930957 := by
    simpa [prefixWord, tailWord_7930957, baseEnd_7930957] using wordTrace_append hprefix tailTrace_7930957
  have hstable : (prefixWord ++ tailWord_7930957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930957).length < 2 ^ (prefixWord ++ tailWord_7930957).sum := by decide
  have hdescent : baseEnd_7930957 < baseStart_7930957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930984 : List Nat := [2, 1, 4, 4, 1, 1, 3, 1, 2, 4]
def baseStart_7930984 : Nat := 118140960795 + 7930984 * 2 ^ 59
def prefixEnd_7930984 : Nat := 4983230072969 + 3 ^ 40 * 7930984 * 2
def baseEnd_7930984 : Nat := 1357468951706034407442025

theorem tailTrace_7930984 : CollatzResearch.WordTrace tailWord_7930984 prefixEnd_7930984 1357468951706034407442025 := by
  unfold tailWord_7930984
  simp only [CollatzResearch.WordTrace]
  refine ⟨144633375349703473537360003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192844500466271298049813337 144633375349703473537360003)
  ·
    refine ⟨216950063024555210306040005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144633375349703473537360003 216950063024555210306040005)
    ·
      refine ⟨40678136817104101932382501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216950063024555210306040005 40678136817104101932382501)
      ·
        refine ⟨7627150653207019112321719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40678136817104101932382501 7627150653207019112321719)
        ·
          refine ⟨11440725979810528668482579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7627150653207019112321719 11440725979810528668482579)
          ·
            refine ⟨17161088969715793002723869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11440725979810528668482579 17161088969715793002723869)
            ·
              refine ⟨6435408363643422376021451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17161088969715793002723869 6435408363643422376021451)
              ·
                refine ⟨9653112545465133564032177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6435408363643422376021451 9653112545465133564032177)
                ·
                  refine ⟨7239834409098850173024133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9653112545465133564032177 7239834409098850173024133)
                  ·
                    refine ⟨1357468951706034407442025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7239834409098850173024133 1357468951706034407442025)
                    ·
                      rfl

theorem cell23_7930984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_7930984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930984 prefixEnd_7930984 := by exact prefixLift 7930984
  have htrace : WordTrace (prefixWord ++ tailWord_7930984) baseStart_7930984 baseEnd_7930984 := by
    simpa [prefixWord, tailWord_7930984, baseEnd_7930984] using wordTrace_append hprefix tailTrace_7930984
  have hstable : (prefixWord ++ tailWord_7930984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930984).length < 2 ^ (prefixWord ++ tailWord_7930984).sum := by decide
  have hdescent : baseEnd_7930984 < baseStart_7930984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930990 : List Nat := [4, 1, 2, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_7930990 : Nat := 118140960795 + 7930990 * 2 ^ 59
def prefixEnd_7930990 : Nat := 4983230072969 + 3 ^ 40 * 7930990 * 2
def baseEnd_7930990 : Nat := 4072409936002030198851047

theorem tailTrace_7930990 : CollatzResearch.WordTrace tailWord_7930990 prefixEnd_7930990 4072409936002030198851047 := by
  unfold tailWord_7930990
  simp only [CollatzResearch.WordTrace]
  refine ⟨36158371192173151262429803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192844646358256806732958949 36158371192173151262429803)
  ·
    refine ⟨54237556788259726893644705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36158371192173151262429803 54237556788259726893644705)
    ·
      refine ⟨40678167591194795170233529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54237556788259726893644705 40678167591194795170233529)
      ·
        refine ⟨30508625693396096377675147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40678167591194795170233529 30508625693396096377675147)
        ·
          refine ⟨45762938540094144566512721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30508625693396096377675147 45762938540094144566512721)
          ·
            refine ⟨34322203905070608424884541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45762938540094144566512721 34322203905070608424884541)
            ·
              refine ⟨12870826464401478159331703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34322203905070608424884541 12870826464401478159331703)
              ·
                refine ⟨19306239696602217238997555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12870826464401478159331703 19306239696602217238997555)
                ·
                  refine ⟨28959359544903325858496333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19306239696602217238997555 28959359544903325858496333)
                  ·
                    refine ⟨10859759829338747196936125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28959359544903325858496333 10859759829338747196936125)
                    ·
                      refine ⟨4072409936002030198851047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10859759829338747196936125 4072409936002030198851047)
                      ·
                        rfl

theorem cell23_7930990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_7930990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930990 prefixEnd_7930990 := by exact prefixLift 7930990
  have htrace : WordTrace (prefixWord ++ tailWord_7930990) baseStart_7930990 baseEnd_7930990 := by
    simpa [prefixWord, tailWord_7930990, baseEnd_7930990] using wordTrace_append hprefix tailTrace_7930990
  have hstable : (prefixWord ++ tailWord_7930990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930990).length < 2 ^ (prefixWord ++ tailWord_7930990).sum := by decide
  have hdescent : baseEnd_7930990 < baseStart_7930990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7930997 : List Nat := [1, 3, 4, 3, 1, 2, 2, 7]
def baseStart_7930997 : Nat := 118140960795 + 7930997 * 2 ^ 59
def prefixEnd_7930997 : Nat := 4983230072969 + 3 ^ 40 * 7930997 * 2
def baseEnd_7930997 : Nat := 150830130754318950794945

theorem tailTrace_7930997 : CollatzResearch.WordTrace tailWord_7930997 prefixEnd_7930997 150830130754318950794945 := by
  unfold tailWord_7930997
  simp only [CollatzResearch.WordTrace]
  refine ⟨289267224848359850294943245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192844816565573233529962163 289267224848359850294943245)
  ·
    refine ⟨108475209318134943860603717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289267224848359850294943245 108475209318134943860603717)
    ·
      refine ⟨20339101747150301973863197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108475209318134943860603717 20339101747150301973863197)
      ·
        refine ⟨7627163155181363240198699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20339101747150301973863197 7627163155181363240198699)
        ·
          refine ⟨11440744732772044860298049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7627163155181363240198699 11440744732772044860298049)
          ·
            refine ⟨8580558549579033645223537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11440744732772044860298049 8580558549579033645223537)
            ·
              refine ⟨6435418912184275233917653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8580558549579033645223537 6435418912184275233917653)
              ·
                refine ⟨150830130754318950794945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6435418912184275233917653 150830130754318950794945)
                ·
                  rfl

theorem cell23_7930997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 7].length) (baseStart_7930997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7930997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7930997 prefixEnd_7930997 := by exact prefixLift 7930997
  have htrace : WordTrace (prefixWord ++ tailWord_7930997) baseStart_7930997 baseEnd_7930997 := by
    simpa [prefixWord, tailWord_7930997, baseEnd_7930997] using wordTrace_append hprefix tailTrace_7930997
  have hstable : (prefixWord ++ tailWord_7930997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7930997).length < 2 ^ (prefixWord ++ tailWord_7930997).sum := by decide
  have hdescent : baseEnd_7930997 < baseStart_7930997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7930997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931000 : List Nat := [2, 1, 2, 1, 1, 1, 5, 4, 1, 3, 2]
def baseStart_7931000 : Nat := 118140960795 + 7931000 * 2 ^ 59
def prefixEnd_7931000 : Nat := 4983230072969 + 3 ^ 40 * 7931000 * 2
def baseEnd_7931000 : Nat := 4072415070808575159726001

theorem tailTrace_7931000 : CollatzResearch.WordTrace tailWord_7931000 prefixEnd_7931000 4072415070808575159726001 := by
  unfold tailWord_7931000
  simp only [CollatzResearch.WordTrace]
  refine ⟨144633667133674490903651227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192844889511565987871534969 144633667133674490903651227)
  ·
    refine ⟨216950500700511736355476841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144633667133674490903651227 216950500700511736355476841)
    ·
      refine ⟨162712875525383802266607631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216950500700511736355476841 162712875525383802266607631)
      ·
        refine ⟨244069313288075703399911447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162712875525383802266607631 244069313288075703399911447)
        ·
          refine ⟨366103969932113555099867171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244069313288075703399911447 366103969932113555099867171)
          ·
            refine ⟨549155954898170332649800757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366103969932113555099867171 549155954898170332649800757)
            ·
              refine ⟨51483370771703468685918821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 549155954898170332649800757 51483370771703468685918821)
              ·
                refine ⟨9653132019694400378609779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51483370771703468685918821 9653132019694400378609779)
                ·
                  refine ⟨14479698029541600567914669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9653132019694400378609779 14479698029541600567914669)
                  ·
                    refine ⟨5429886761078100212968001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14479698029541600567914669 5429886761078100212968001)
                    ·
                      refine ⟨4072415070808575159726001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5429886761078100212968001 4072415070808575159726001)
                      ·
                        rfl

theorem cell23_7931000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 1, 3, 2].length) (baseStart_7931000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931000 prefixEnd_7931000 := by exact prefixLift 7931000
  have htrace : WordTrace (prefixWord ++ tailWord_7931000) baseStart_7931000 baseEnd_7931000 := by
    simpa [prefixWord, tailWord_7931000, baseEnd_7931000] using wordTrace_append hprefix tailTrace_7931000
  have hstable : (prefixWord ++ tailWord_7931000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931000).length < 2 ^ (prefixWord ++ tailWord_7931000).sum := by decide
  have hdescent : baseEnd_7931000 < baseStart_7931000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931050 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_7931050 : Nat := 118140960795 + 7931050 * 2 ^ 59
def prefixEnd_7931050 : Nat := 4983230072969 + 3 ^ 40 * 7931050 * 2
def baseEnd_7931050 : Nat := 4072440744841299964100771

theorem tailTrace_7931050 : CollatzResearch.WordTrace tailWord_7931050 prefixEnd_7931050 4072440744841299964100771 := by
  unfold tailWord_7931050
  simp only [CollatzResearch.WordTrace]
  refine ⟨72317289479291960086655651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192846105278111893564415069 72317289479291960086655651)
  ·
    refine ⟨108475934218937940129983477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72317289479291960086655651 108475934218937940129983477)
    ·
      refine ⟨10169618833025431887185951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108475934218937940129983477 10169618833025431887185951)
      ·
        refine ⟨15254428249538147830778927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10169618833025431887185951 15254428249538147830778927)
        ·
          refine ⟨22881642374307221746168391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15254428249538147830778927 22881642374307221746168391)
          ·
            refine ⟨34322463561460832619252587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22881642374307221746168391 34322463561460832619252587)
            ·
              refine ⟨51483695342191248928878881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34322463561460832619252587 51483695342191248928878881)
              ·
                refine ⟨38612771506643436696659161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51483695342191248928878881 38612771506643436696659161)
                ·
                  refine ⟨28959578629982577522494371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38612771506643436696659161 28959578629982577522494371)
                  ·
                    refine ⟨43439367944973866283741557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28959578629982577522494371 43439367944973866283741557)
                    ·
                      refine ⟨4072440744841299964100771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43439367944973866283741557 4072440744841299964100771)
                      ·
                        rfl

theorem cell23_7931050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_7931050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931050 prefixEnd_7931050 := by exact prefixLift 7931050
  have htrace : WordTrace (prefixWord ++ tailWord_7931050) baseStart_7931050 baseEnd_7931050 := by
    simpa [prefixWord, tailWord_7931050, baseEnd_7931050] using wordTrace_append hprefix tailTrace_7931050
  have hstable : (prefixWord ++ tailWord_7931050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931050).length < 2 ^ (prefixWord ++ tailWord_7931050).sum := by decide
  have hdescent : baseEnd_7931050 < baseStart_7931050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931090 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 1, 7, 2]
def baseStart_7931090 : Nat := 118140960795 + 7931090 * 2 ^ 59
def prefixEnd_7931090 : Nat := 4983230072969 + 3 ^ 40 * 7931090 * 2
def baseEnd_7931090 : Nat := 4072461284067479807600587

theorem tailTrace_7931090 : CollatzResearch.WordTrace tailWord_7931090 prefixEnd_7931090 4072461284067479807600587 := by
  unfold tailWord_7931090
  simp only [CollatzResearch.WordTrace]
  refine ⟨72317654209255731794519681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192847077891348618118719149 72317654209255731794519681)
  ·
    refine ⟨54238240656941798845889761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72317654209255731794519681 54238240656941798845889761)
    ·
      refine ⟨40678680492706349134417321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54238240656941798845889761 40678680492706349134417321)
      ·
        refine ⟨30509010369529761850812991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40678680492706349134417321 30509010369529761850812991)
        ·
          refine ⟨45763515554294642776219487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30509010369529761850812991 45763515554294642776219487)
          ·
            refine ⟨68645273331441964164329231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45763515554294642776219487 68645273331441964164329231)
            ·
              refine ⟨102967909997162946246493847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68645273331441964164329231 102967909997162946246493847)
              ·
                refine ⟨154451864995744419369740771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102967909997162946246493847 154451864995744419369740771)
                ·
                  refine ⟨231677797493616629054611157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154451864995744419369740771 231677797493616629054611157)
                  ·
                    refine ⟨5429948378756639743467449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 231677797493616629054611157 5429948378756639743467449)
                    ·
                      refine ⟨4072461284067479807600587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5429948378756639743467449 4072461284067479807600587)
                      ·
                        rfl

theorem cell23_7931090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_7931090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931090 prefixEnd_7931090 := by exact prefixLift 7931090
  have htrace : WordTrace (prefixWord ++ tailWord_7931090) baseStart_7931090 baseEnd_7931090 := by
    simpa [prefixWord, tailWord_7931090, baseEnd_7931090] using wordTrace_append hprefix tailTrace_7931090
  have hstable : (prefixWord ++ tailWord_7931090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931090).length < 2 ^ (prefixWord ++ tailWord_7931090).sum := by decide
  have hdescent : baseEnd_7931090 < baseStart_7931090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931103 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 4]
def baseStart_7931103 : Nat := 118140960795 + 7931103 * 2 ^ 59
def prefixEnd_7931103 : Nat := 4983230072969 + 3 ^ 40 * 7931103 * 2
def baseEnd_7931103 : Nat := 4072467959315988256738027

theorem tailTrace_7931103 : CollatzResearch.WordTrace tailWord_7931103 prefixEnd_7931103 4072467959315988256738027 := by
  unfold tailWord_7931103
  simp only [CollatzResearch.WordTrace]
  refine ⟨289271090985975830398301963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192847393990650553598867975 289271090985975830398301963)
  ·
    refine ⟨433906636478963745597452945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289271090985975830398301963 433906636478963745597452945)
    ·
      refine ⟨325429977359222809198089709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433906636478963745597452945 325429977359222809198089709)
      ·
        refine ⟨122036241509708553449283641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325429977359222809198089709 122036241509708553449283641)
        ·
          refine ⟨91527181132281415086962731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122036241509708553449283641 91527181132281415086962731)
          ·
            refine ⟨137290771698422122630444097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91527181132281415086962731 137290771698422122630444097)
            ·
              refine ⟨102968078773816591972833073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137290771698422122630444097 102968078773816591972833073)
              ·
                refine ⟨77226059080362443979624805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102968078773816591972833073 77226059080362443979624805)
                ·
                  refine ⟨14479886077567958246179651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77226059080362443979624805 14479886077567958246179651)
                  ·
                    refine ⟨21719829116351937369269477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14479886077567958246179651 21719829116351937369269477)
                    ·
                      refine ⟨4072467959315988256738027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21719829116351937369269477 4072467959315988256738027)
                      ·
                        rfl

theorem cell23_7931103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_7931103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931103 prefixEnd_7931103 := by exact prefixLift 7931103
  have htrace : WordTrace (prefixWord ++ tailWord_7931103) baseStart_7931103 baseEnd_7931103 := by
    simpa [prefixWord, tailWord_7931103, baseEnd_7931103] using wordTrace_append hprefix tailTrace_7931103
  have hstable : (prefixWord ++ tailWord_7931103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931103).length < 2 ^ (prefixWord ++ tailWord_7931103).sum := by decide
  have hdescent : baseEnd_7931103 < baseStart_7931103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931117 : List Nat := [1, 5, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_7931117 : Nat := 118140960795 + 7931117 * 2 ^ 59
def prefixEnd_7931117 : Nat := 4983230072969 + 3 ^ 40 * 7931117 * 2
def baseEnd_7931117 : Nat := 1357491716015050400654321

theorem tailTrace_7931117 : CollatzResearch.WordTrace tailWord_7931117 prefixEnd_7931117 1357491716015050400654321 := by
  unfold tailWord_7931117
  simp only [CollatzResearch.WordTrace]
  refine ⟨289271601607925110789311605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192847734405283407192874403 289271601607925110789311605)
  ·
    refine ⟨27119212650742979136497963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289271601607925110789311605 27119212650742979136497963)
    ·
      refine ⟨40678818976114468704746945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27119212650742979136497963 40678818976114468704746945)
      ·
        refine ⟨30509114232085851528560209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40678818976114468704746945 30509114232085851528560209)
        ·
          refine ⟨22881835674064388646420157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30509114232085851528560209 22881835674064388646420157)
          ·
            refine ⟨8580688377774145742407559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22881835674064388646420157 8580688377774145742407559)
            ·
              refine ⟨12871032566661218613611339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8580688377774145742407559 12871032566661218613611339)
              ·
                refine ⟨19306548849991827920417009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12871032566661218613611339 19306548849991827920417009)
                ·
                  refine ⟨14479911637493870940312757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19306548849991827920417009 14479911637493870940312757)
                  ·
                    refine ⟨1357491716015050400654321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14479911637493870940312757 1357491716015050400654321)
                    ·
                      rfl

theorem cell23_7931117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_7931117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931117 prefixEnd_7931117 := by exact prefixLift 7931117
  have htrace : WordTrace (prefixWord ++ tailWord_7931117) baseStart_7931117 baseEnd_7931117 := by
    simpa [prefixWord, tailWord_7931117, baseEnd_7931117] using wordTrace_append hprefix tailTrace_7931117
  have hstable : (prefixWord ++ tailWord_7931117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931117).length < 2 ^ (prefixWord ++ tailWord_7931117).sum := by decide
  have hdescent : baseEnd_7931117 < baseStart_7931117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931147 : List Nat := [1, 1, 1, 1, 5, 3, 2, 4, 1, 4]
def baseStart_7931147 : Nat := 118140960795 + 7931147 * 2 ^ 59
def prefixEnd_7931147 : Nat := 4983230072969 + 3 ^ 40 * 7931147 * 2
def baseEnd_7931147 : Nat := 1357496850821595361529275

theorem tailTrace_7931147 : CollatzResearch.WordTrace tailWord_7931147 prefixEnd_7931147 1357496850821595361529275 := by
  unfold tailWord_7931147
  simp only [CollatzResearch.WordTrace]
  refine ⟨289272695797816425912903695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192848463865210950608602463 289272695797816425912903695)
  ·
    refine ⟨433909043696724638869355543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289272695797816425912903695 433909043696724638869355543)
    ·
      refine ⟨650863565545086958304033315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433909043696724638869355543 650863565545086958304033315)
      ·
        refine ⟨976295348317630437456049973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650863565545086958304033315 976295348317630437456049973)
        ·
          refine ⟨91527688904777853511504685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 976295348317630437456049973 91527688904777853511504685)
          ·
            refine ⟨34322883339291695066814257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91527688904777853511504685 34322883339291695066814257)
            ·
              refine ⟨25742162504468771300110693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34322883339291695066814257 25742162504468771300110693)
              ·
                refine ⟨4826655469587894618770755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25742162504468771300110693 4826655469587894618770755)
                ·
                  refine ⟨7239983204381841928156133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4826655469587894618770755 7239983204381841928156133)
                  ·
                    refine ⟨1357496850821595361529275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7239983204381841928156133 1357496850821595361529275)
                    ·
                      rfl

theorem cell23_7931147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 1, 4].length) (baseStart_7931147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931147 prefixEnd_7931147 := by exact prefixLift 7931147
  have htrace : WordTrace (prefixWord ++ tailWord_7931147) baseStart_7931147 baseEnd_7931147 := by
    simpa [prefixWord, tailWord_7931147, baseEnd_7931147] using wordTrace_append hprefix tailTrace_7931147
  have hstable : (prefixWord ++ tailWord_7931147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931147).length < 2 ^ (prefixWord ++ tailWord_7931147).sum := by decide
  have hdescent : baseEnd_7931147 < baseStart_7931147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931181 : List Nat := [1, 5, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_7931181 : Nat := 118140960795 + 7931181 * 2 ^ 59
def prefixEnd_7931181 : Nat := 4983230072969 + 3 ^ 40 * 7931181 * 2
def baseEnd_7931181 : Nat := 1357502670269012983854223

theorem tailTrace_7931181 : CollatzResearch.WordTrace tailWord_7931181 prefixEnd_7931181 1357502670269012983854223 := by
  unfold tailWord_7931181
  simp only [CollatzResearch.WordTrace]
  refine ⟨289273935879693249719641397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192849290586462166479760931 289273935879693249719641397)
  ·
    refine ⟨27119431488721242161216381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289273935879693249719641397 27119431488721242161216381)
    ·
      refine ⟨10169786808270465810456143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27119431488721242161216381 10169786808270465810456143)
      ·
        refine ⟨15254680212405698715684215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10169786808270465810456143 15254680212405698715684215)
        ·
          refine ⟨22882020318608548073526323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15254680212405698715684215 22882020318608548073526323)
          ·
            refine ⟨34323030477912822110289485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22882020318608548073526323 34323030477912822110289485)
            ·
              refine ⟨12871136429217308291358557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34323030477912822110289485 12871136429217308291358557)
              ·
                refine ⟨4826676160956490609259459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12871136429217308291358557 4826676160956490609259459)
                ·
                  refine ⟨7240014241434735913889189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4826676160956490609259459 7240014241434735913889189)
                  ·
                    refine ⟨1357502670269012983854223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7240014241434735913889189 1357502670269012983854223)
                    ·
                      rfl

theorem cell23_7931181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_7931181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931181 prefixEnd_7931181 := by exact prefixLift 7931181
  have htrace : WordTrace (prefixWord ++ tailWord_7931181) baseStart_7931181 baseEnd_7931181 := by
    simpa [prefixWord, tailWord_7931181, baseEnd_7931181] using wordTrace_append hprefix tailTrace_7931181
  have hstable : (prefixWord ++ tailWord_7931181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931181).length < 2 ^ (prefixWord ++ tailWord_7931181).sum := by decide
  have hdescent : baseEnd_7931181 < baseStart_7931181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931220 : List Nat := [2, 4, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_7931220 : Nat := 118140960795 + 7931220 * 2 ^ 59
def prefixEnd_7931220 : Nat := 4983230072969 + 3 ^ 40 * 7931220 * 2
def baseEnd_7931220 : Nat := 1357509345517521432991663

theorem tailTrace_7931220 : CollatzResearch.WordTrace tailWord_7931220 prefixEnd_7931220 1357509345517521432991663 := by
  unfold tailWord_7931220
  simp only [CollatzResearch.WordTrace]
  refine ⟨144637679163275979690155557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192850238884367972920207409 144637679163275979690155557)
  ·
    refine ⟨27119564843114246191904167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144637679163275979690155557 27119564843114246191904167)
    ·
      refine ⟨40679347264671369287856251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27119564843114246191904167 40679347264671369287856251)
      ·
        refine ⟨61019020897007053931784377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40679347264671369287856251 61019020897007053931784377)
        ·
          refine ⟨45764265672755290448838283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61019020897007053931784377 45764265672755290448838283)
          ·
            refine ⟨68646398509132935673257425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45764265672755290448838283 68646398509132935673257425)
            ·
              refine ⟨51484798881849701754943069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68646398509132935673257425 51484798881849701754943069)
              ·
                refine ⟨19306799580693638158103651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51484798881849701754943069 19306799580693638158103651)
                ·
                  refine ⟨28960199371040457237155477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19306799580693638158103651 28960199371040457237155477)
                  ·
                    refine ⟨1357509345517521432991663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28960199371040457237155477 1357509345517521432991663)
                    ·
                      rfl

theorem cell23_7931220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_7931220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931220 prefixEnd_7931220 := by exact prefixLift 7931220
  have htrace : WordTrace (prefixWord ++ tailWord_7931220) baseStart_7931220 baseEnd_7931220 := by
    simpa [prefixWord, tailWord_7931220, baseEnd_7931220] using wordTrace_append hprefix tailTrace_7931220
  have hstable : (prefixWord ++ tailWord_7931220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931220).length < 2 ^ (prefixWord ++ tailWord_7931220).sum := by decide
  have hdescent : baseEnd_7931220 < baseStart_7931220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931244 : List Nat := [2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 4]
def baseStart_7931244 : Nat := 118140960795 + 7931244 * 2 ^ 59
def prefixEnd_7931244 : Nat := 4983230072969 + 3 ^ 40 * 7931244 * 2
def baseEnd_7931244 : Nat := 4072540360088272205074879

theorem tailTrace_7931244 : CollatzResearch.WordTrace tailWord_7931244 prefixEnd_7931244 4072540360088272205074879 := by
  unfold tailWord_7931244
  simp only [CollatzResearch.WordTrace]
  refine ⟨144638116839232505739592393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192850822452310007652789857 144638116839232505739592393)
  ·
    refine ⟨108478587629424379304694295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144638116839232505739592393 108478587629424379304694295)
    ·
      refine ⟨162717881444136568957041443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108478587629424379304694295 162717881444136568957041443)
      ·
        refine ⟨244076822166204853435562165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162717881444136568957041443 244076822166204853435562165)
        ·
          refine ⟨22882202078081705009583953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 244076822166204853435562165 22882202078081705009583953)
          ·
            refine ⟨17161651558561278757187965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22882202078081705009583953 17161651558561278757187965)
            ·
              refine ⟨6435619334460479533945487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17161651558561278757187965 6435619334460479533945487)
              ·
                refine ⟨9653429001690719300918231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6435619334460479533945487 9653429001690719300918231)
                ·
                  refine ⟨14480143502536078951377347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9653429001690719300918231 14480143502536078951377347)
                  ·
                    refine ⟨21720215253804118427066021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14480143502536078951377347 21720215253804118427066021)
                    ·
                      refine ⟨4072540360088272205074879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21720215253804118427066021 4072540360088272205074879)
                      ·
                        rfl

theorem cell23_7931244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 4].length) (baseStart_7931244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931244 prefixEnd_7931244 := by exact prefixLift 7931244
  have htrace : WordTrace (prefixWord ++ tailWord_7931244) baseStart_7931244 baseEnd_7931244 := by
    simpa [prefixWord, tailWord_7931244, baseEnd_7931244] using wordTrace_append hprefix tailTrace_7931244
  have hstable : (prefixWord ++ tailWord_7931244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931244).length < 2 ^ (prefixWord ++ tailWord_7931244).sum := by decide
  have hdescent : baseEnd_7931244 < baseStart_7931244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931260 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 3, 3, 3]
def baseStart_7931260 : Nat := 118140960795 + 7931260 * 2 ^ 59
def prefixEnd_7931260 : Nat := 4983230072969 + 3 ^ 40 * 7931260 * 2
def baseEnd_7931260 : Nat := 4072548575778744142474805

theorem tailTrace_7931260 : CollatzResearch.WordTrace tailWord_7931260 prefixEnd_7931260 4072548575778744142474805 := by
  unfold tailWord_7931260
  simp only [CollatzResearch.WordTrace]
  refine ⟨144638408623203523105883617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192851211497604697474511489 144638408623203523105883617)
  ·
    refine ⟨108478806467402642329412713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144638408623203523105883617 108478806467402642329412713)
    ·
      refine ⟨81359104850551981747059535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108478806467402642329412713 81359104850551981747059535)
      ·
        refine ⟨122038657275827972620589303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81359104850551981747059535 122038657275827972620589303)
        ·
          refine ⟨183057985913741958930883955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122038657275827972620589303 183057985913741958930883955)
          ·
            refine ⟨274586978870612938396325933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183057985913741958930883955 274586978870612938396325933)
            ·
              refine ⟨102970117076479851898622225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274586978870612938396325933 102970117076479851898622225)
              ·
                refine ⟨77227587807359888923966669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102970117076479851898622225 77227587807359888923966669)
                ·
                  refine ⟨28960345427759958346487501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77227587807359888923966669 28960345427759958346487501)
                  ·
                    refine ⟨10860129535409984379932813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28960345427759958346487501 10860129535409984379932813)
                    ·
                      refine ⟨4072548575778744142474805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10860129535409984379932813 4072548575778744142474805)
                      ·
                        rfl

theorem cell23_7931260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_7931260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931260 prefixEnd_7931260 := by exact prefixLift 7931260
  have htrace : WordTrace (prefixWord ++ tailWord_7931260) baseStart_7931260 baseEnd_7931260 := by
    simpa [prefixWord, tailWord_7931260, baseEnd_7931260] using wordTrace_append hprefix tailTrace_7931260
  have hstable : (prefixWord ++ tailWord_7931260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931260).length < 2 ^ (prefixWord ++ tailWord_7931260).sum := by decide
  have hdescent : baseEnd_7931260 < baseStart_7931260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931261 : List Nat := [1, 4, 1, 1, 2, 2, 3, 4, 1, 2, 2]
def baseStart_7931261 : Nat := 118140960795 + 7931261 * 2 ^ 59
def prefixEnd_7931261 : Nat := 4983230072969 + 3 ^ 40 * 7931261 * 2
def baseEnd_7931261 : Nat := 4072549089259398638562301

theorem tailTrace_7931261 : CollatzResearch.WordTrace tailWord_7931261 prefixEnd_7931261 4072549089259398638562301 := by
  unfold tailWord_7931261
  simp only [CollatzResearch.WordTrace]
  refine ⟨289276853719403423382553637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192851235812935615588369091 289276853719403423382553637)
  ·
    refine ⟨54239410072388141884228807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289276853719403423382553637 54239410072388141884228807)
    ·
      refine ⟨81359115108582212826343211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54239410072388141884228807 81359115108582212826343211)
      ·
        refine ⟨122038672662873319239514817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81359115108582212826343211 122038672662873319239514817)
        ·
          refine ⟨91529004497154989429636113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122038672662873319239514817 91529004497154989429636113)
          ·
            refine ⟨68646753372866242072227085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91529004497154989429636113 68646753372866242072227085)
            ·
              refine ⟨25742532514824840777085157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68646753372866242072227085 25742532514824840777085157)
              ·
                refine ⟨4826724846529657645703467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25742532514824840777085157 4826724846529657645703467)
                ·
                  refine ⟨7240087269794486468555201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4826724846529657645703467 7240087269794486468555201)
                  ·
                    refine ⟨5430065452345864851416401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7240087269794486468555201 5430065452345864851416401)
                    ·
                      refine ⟨4072549089259398638562301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5430065452345864851416401 4072549089259398638562301)
                      ·
                        rfl

theorem cell23_7931261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_7931261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931261 prefixEnd_7931261 := by exact prefixLift 7931261
  have htrace : WordTrace (prefixWord ++ tailWord_7931261) baseStart_7931261 baseEnd_7931261 := by
    simpa [prefixWord, tailWord_7931261, baseEnd_7931261] using wordTrace_append hprefix tailTrace_7931261
  have hstable : (prefixWord ++ tailWord_7931261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931261).length < 2 ^ (prefixWord ++ tailWord_7931261).sum := by decide
  have hdescent : baseEnd_7931261 < baseStart_7931261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931290 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5]
def baseStart_7931290 : Nat := 118140960795 + 7931290 * 2 ^ 59
def prefixEnd_7931290 : Nat := 4983230072969 + 3 ^ 40 * 7931290 * 2
def baseEnd_7931290 : Nat := 4072563980198379025099667

theorem tailTrace_7931290 : CollatzResearch.WordTrace tailWord_7931290 prefixEnd_7931290 4072563980198379025099667 := by
  unfold tailWord_7931290
  simp only [CollatzResearch.WordTrace]
  refine ⟨72319477859074590333839831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192851940957532240890239549 72319477859074590333839831)
  ·
    refine ⟨108479216788611885500759747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72319477859074590333839831 108479216788611885500759747)
    ·
      refine ⟨162718825182917828251139621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108479216788611885500759747 162718825182917828251139621)
      ·
        refine ⟨30509779721797092797088679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162718825182917828251139621 30509779721797092797088679)
        ·
          refine ⟨45764669582695639195633019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30509779721797092797088679 45764669582695639195633019)
          ·
            refine ⟨68647004374043458793449529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45764669582695639195633019 68647004374043458793449529)
            ·
              refine ⟨51485253280532594095087147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68647004374043458793449529 51485253280532594095087147)
              ·
                refine ⟨77227879920798891142630721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51485253280532594095087147 77227879920798891142630721)
                ·
                  refine ⟨57920909940599168356973041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77227879920798891142630721 57920909940599168356973041)
                  ·
                    refine ⟨43440682455449376267729781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57920909940599168356973041 43440682455449376267729781)
                    ·
                      refine ⟨4072563980198379025099667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43440682455449376267729781 4072563980198379025099667)
                      ·
                        rfl

theorem cell23_7931290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_7931290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931290 prefixEnd_7931290 := by exact prefixLift 7931290
  have htrace : WordTrace (prefixWord ++ tailWord_7931290) baseStart_7931290 baseEnd_7931290 := by
    simpa [prefixWord, tailWord_7931290, baseEnd_7931290] using wordTrace_append hprefix tailTrace_7931290
  have hstable : (prefixWord ++ tailWord_7931290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931290).length < 2 ^ (prefixWord ++ tailWord_7931290).sum := by decide
  have hdescent : baseEnd_7931290 < baseStart_7931290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931320 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 1, 6, 3]
def baseStart_7931320 : Nat := 118140960795 + 7931320 * 2 ^ 59
def prefixEnd_7931320 : Nat := 4983230072969 + 3 ^ 40 * 7931320 * 2
def baseEnd_7931320 : Nat := 4072579384618013907724529

theorem tailTrace_7931320 : CollatzResearch.WordTrace tailWord_7931320 prefixEnd_7931320 4072579384618013907724529 := by
  unfold tailWord_7931320
  simp only [CollatzResearch.WordTrace]
  refine ⟨144639502813094838229475707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192852670417459784305967609 144639502813094838229475707)
  ·
    refine ⟨216959254219642257344213561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144639502813094838229475707 216959254219642257344213561)
    ·
      refine ⟨162719440664731693008160171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216959254219642257344213561 162719440664731693008160171)
      ·
        refine ⟨244079160997097539512240257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162719440664731693008160171 244079160997097539512240257)
        ·
          refine ⟨183059370747823154634180193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244079160997097539512240257 183059370747823154634180193)
          ·
            refine ⟨137294528060867365975635145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183059370747823154634180193 137294528060867365975635145)
            ·
              refine ⟨102970896045650524481726359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137294528060867365975635145 102970896045650524481726359)
              ·
                refine ⟨154456344068475786722589539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102970896045650524481726359 154456344068475786722589539)
                ·
                  refine ⟨231684516102713680083884309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154456344068475786722589539 231684516102713680083884309)
                  ·
                    refine ⟨10860211692314703753932077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 231684516102713680083884309 10860211692314703753932077)
                    ·
                      refine ⟨4072579384618013907724529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10860211692314703753932077 4072579384618013907724529)
                      ·
                        rfl

theorem cell23_7931320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_7931320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931320 prefixEnd_7931320 := by exact prefixLift 7931320
  have htrace : WordTrace (prefixWord ++ tailWord_7931320) baseStart_7931320 baseEnd_7931320 := by
    simpa [prefixWord, tailWord_7931320, baseEnd_7931320] using wordTrace_append hprefix tailTrace_7931320
  have hstable : (prefixWord ++ tailWord_7931320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931320).length < 2 ^ (prefixWord ++ tailWord_7931320).sum := by decide
  have hdescent : baseEnd_7931320 < baseStart_7931320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931400 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 2, 8]
def baseStart_7931400 : Nat := 118140960795 + 7931400 * 2 ^ 59
def prefixEnd_7931400 : Nat := 4983230072969 + 3 ^ 40 * 7931400 * 2
def baseEnd_7931400 : Nat := 1357540154356791198241387

theorem tailTrace_7931400 : CollatzResearch.WordTrace tailWord_7931400 prefixEnd_7931400 1357540154356791198241387 := by
  unfold tailWord_7931400
  simp only [CollatzResearch.WordTrace]
  refine ⟨144640961732949925060931827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192854615643933233414575769 144640961732949925060931827)
  ·
    refine ⟨216961442599424887591397741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144640961732949925060931827 216961442599424887591397741)
    ·
      refine ⟨81360540974784332846774153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216961442599424887591397741 81360540974784332846774153)
      ·
        refine ⟨61020405731088249635080615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81360540974784332846774153 61020405731088249635080615)
        ·
          refine ⟨91530608596632374452620923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61020405731088249635080615 91530608596632374452620923)
          ·
            refine ⟨137295912894948561678931385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91530608596632374452620923 137295912894948561678931385)
            ·
              refine ⟨102971934671211421259198539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137295912894948561678931385 102971934671211421259198539)
              ·
                refine ⟨154457902006817131888797809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102971934671211421259198539 154457902006817131888797809)
                ·
                  refine ⟨115843426505112848916598357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154457902006817131888797809 115843426505112848916598357)
                  ·
                    refine ⟨1357540154356791198241387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115843426505112848916598357 1357540154356791198241387)
                    ·
                      rfl

theorem cell23_7931400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_7931400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931400 prefixEnd_7931400 := by exact prefixLift 7931400
  have htrace : WordTrace (prefixWord ++ tailWord_7931400) baseStart_7931400 baseEnd_7931400 := by
    simpa [prefixWord, tailWord_7931400, baseEnd_7931400] using wordTrace_append hprefix tailTrace_7931400
  have hstable : (prefixWord ++ tailWord_7931400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931400).length < 2 ^ (prefixWord ++ tailWord_7931400).sum := by decide
  have hdescent : baseEnd_7931400 < baseStart_7931400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931404 : List Nat := [2, 2, 1, 2, 5, 1, 2, 1, 2, 5]
def baseStart_7931404 : Nat := 118140960795 + 7931404 * 2 ^ 59
def prefixEnd_7931404 : Nat := 4983230072969 + 3 ^ 40 * 7931404 * 2
def baseEnd_7931404 : Nat := 1357540838997663859691381

theorem tailTrace_7931404 : CollatzResearch.WordTrace tailWord_7931404 prefixEnd_7931404 1357540838997663859691381 := by
  unfold tailWord_7931404
  simp only [CollatzResearch.WordTrace]
  refine ⟨144641034678942679402504633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192854712905256905870006177 144641034678942679402504633)
  ·
    refine ⟨108480776009207009551878475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144641034678942679402504633 108480776009207009551878475)
    ·
      refine ⟨162721164013810514327817713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108480776009207009551878475 162721164013810514327817713)
      ·
        refine ⟨122040873010357885745863285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162721164013810514327817713 122040873010357885745863285)
        ·
          refine ⟨11441331844721051788674683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122040873010357885745863285 11441331844721051788674683)
          ·
            refine ⟨17161997767081577683012025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11441331844721051788674683 17161997767081577683012025)
            ·
              refine ⟨12871498325311183262259019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17161997767081577683012025 12871498325311183262259019)
              ·
                refine ⟨19307247487966774893388529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12871498325311183262259019 19307247487966774893388529)
                ·
                  refine ⟨14480435615975081170041397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19307247487966774893388529 14480435615975081170041397)
                  ·
                    refine ⟨1357540838997663859691381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14480435615975081170041397 1357540838997663859691381)
                    ·
                      rfl

theorem cell23_7931404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_7931404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931404 prefixEnd_7931404 := by exact prefixLift 7931404
  have htrace : WordTrace (prefixWord ++ tailWord_7931404) baseStart_7931404 baseEnd_7931404 := by
    simpa [prefixWord, tailWord_7931404, baseEnd_7931404] using wordTrace_append hprefix tailTrace_7931404
  have hstable : (prefixWord ++ tailWord_7931404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931404).length < 2 ^ (prefixWord ++ tailWord_7931404).sum := by decide
  have hdescent : baseEnd_7931404 < baseStart_7931404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931424 : List Nat := [2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 4]
def baseStart_7931424 : Nat := 118140960795 + 7931424 * 2 ^ 59
def prefixEnd_7931424 : Nat := 4983230072969 + 3 ^ 40 * 7931424 * 2
def baseEnd_7931424 : Nat := 4072632786606081500824051

theorem tailTrace_7931424 : CollatzResearch.WordTrace tailWord_7931424 prefixEnd_7931424 4072632786606081500824051 := by
  unfold tailWord_7931424
  simp only [CollatzResearch.WordTrace]
  refine ⟨144641399408906451110368663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192855199211875268147158217 144641399408906451110368663)
  ·
    refine ⟨216962099113359676665552995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144641399408906451110368663 216962099113359676665552995)
    ·
      refine ⟨325443148670039514998329493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216962099113359676665552995 325443148670039514998329493)
      ·
        refine ⟨15255147593908102265546695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 325443148670039514998329493 15255147593908102265546695)
        ·
          refine ⟨22882721390862153398320043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15255147593908102265546695 22882721390862153398320043)
          ·
            refine ⟨34324082086293230097480065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22882721390862153398320043 34324082086293230097480065)
            ·
              refine ⟨25743061564719922573110049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34324082086293230097480065 25743061564719922573110049)
              ·
                refine ⟨19307296173539941929832537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25743061564719922573110049 19307296173539941929832537)
                ·
                  refine ⟨14480472130154956447374403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19307296173539941929832537 14480472130154956447374403)
                  ·
                    refine ⟨21720708195232434671061605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14480472130154956447374403 21720708195232434671061605)
                    ·
                      refine ⟨4072632786606081500824051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21720708195232434671061605 4072632786606081500824051)
                      ·
                        rfl

theorem cell23_7931424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_7931424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931424 prefixEnd_7931424 := by exact prefixLift 7931424
  have htrace : WordTrace (prefixWord ++ tailWord_7931424) baseStart_7931424 baseEnd_7931424 := by
    simpa [prefixWord, tailWord_7931424, baseEnd_7931424] using wordTrace_append hprefix tailTrace_7931424
  have hstable : (prefixWord ++ tailWord_7931424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931424).length < 2 ^ (prefixWord ++ tailWord_7931424).sum := by decide
  have hdescent : baseEnd_7931424 < baseStart_7931424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931434 : List Nat := [3, 1, 4, 1, 1, 1, 2, 3, 3, 4]
def baseStart_7931434 : Nat := 118140960795 + 7931434 * 2 ^ 59
def prefixEnd_7931434 : Nat := 4983230072969 + 3 ^ 40 * 7931434 * 2
def baseEnd_7931434 : Nat := 1357545973804208820566335

theorem tailTrace_7931434 : CollatzResearch.WordTrace tailWord_7931434 prefixEnd_7931434 1357545973804208820566335 := by
  unfold tailWord_7931434
  simp only [CollatzResearch.WordTrace]
  refine ⟨72320790886944168482150339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192855442365184449285734237 72320790886944168482150339)
  ·
    refine ⟨108481186330416252723225509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72320790886944168482150339 108481186330416252723225509)
    ·
      refine ⟨20340222436953047385604783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108481186330416252723225509 20340222436953047385604783)
      ·
        refine ⟨30510333655429571078407175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20340222436953047385604783 30510333655429571078407175)
        ·
          refine ⟨45765500483144356617610763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30510333655429571078407175 45765500483144356617610763)
          ·
            refine ⟨68648250724716534926416145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45765500483144356617610763 68648250724716534926416145)
            ·
              refine ⟨51486188043537401194812109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68648250724716534926416145 51486188043537401194812109)
              ·
                refine ⟨19307320516326525448054541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51486188043537401194812109 19307320516326525448054541)
                ·
                  refine ⟨7240245193622447043020453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19307320516326525448054541 7240245193622447043020453)
                  ·
                    refine ⟨1357545973804208820566335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7240245193622447043020453 1357545973804208820566335)
                    ·
                      rfl

theorem cell23_7931434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_7931434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931434 prefixEnd_7931434 := by exact prefixLift 7931434
  have htrace : WordTrace (prefixWord ++ tailWord_7931434) baseStart_7931434 baseEnd_7931434 := by
    simpa [prefixWord, tailWord_7931434, baseEnd_7931434] using wordTrace_append hprefix tailTrace_7931434
  have hstable : (prefixWord ++ tailWord_7931434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931434).length < 2 ^ (prefixWord ++ tailWord_7931434).sum := by decide
  have hdescent : baseEnd_7931434 < baseStart_7931434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931447 : List Nat := [1, 1, 3, 1, 2, 4, 2, 3, 6]
def baseStart_7931447 : Nat := 118140960795 + 7931447 * 2 ^ 59
def prefixEnd_7931447 : Nat := 4983230072969 + 3 ^ 40 * 7931447 * 2
def baseEnd_7931447 : Nat := 452516066295681656759605

theorem tailTrace_7931447 : CollatzResearch.WordTrace tailWord_7931447 prefixEnd_7931447 452516066295681656759605 := by
  unfold tailWord_7931447
  simp only [CollatzResearch.WordTrace]
  refine ⟨289283637696729577148824595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192855758464486384765883063 289283637696729577148824595)
  ·
    refine ⟨433925456545094365723236893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289283637696729577148824595 433925456545094365723236893)
    ·
      refine ⟨162722046204410387146213835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433925456545094365723236893 162722046204410387146213835)
      ·
        refine ⟨244083069306615580719320753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162722046204410387146213835 244083069306615580719320753)
        ·
          refine ⟨183062301979961685539490565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244083069306615580719320753 183062301979961685539490565)
          ·
            refine ⟨34324181621242816038654481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183062301979961685539490565 34324181621242816038654481)
            ·
              refine ⟨25743136215932112028990861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34324181621242816038654481 25743136215932112028990861)
              ·
                refine ⟨9653676080974542010871573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25743136215932112028990861 9653676080974542010871573)
                ·
                  refine ⟨452516066295681656759605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9653676080974542010871573 452516066295681656759605)
                  ·
                    rfl

theorem cell23_7931447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 6].length) (baseStart_7931447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931447 prefixEnd_7931447 := by exact prefixLift 7931447
  have htrace : WordTrace (prefixWord ++ tailWord_7931447) baseStart_7931447 baseEnd_7931447 := by
    simpa [prefixWord, tailWord_7931447, baseEnd_7931447] using wordTrace_append hprefix tailTrace_7931447
  have hstable : (prefixWord ++ tailWord_7931447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931447).length < 2 ^ (prefixWord ++ tailWord_7931447).sum := by decide
  have hdescent : baseEnd_7931447 < baseStart_7931447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931491 : List Nat := [1, 1, 1, 5, 1, 4, 2, 1, 3, 1, 3]
def baseStart_7931491 : Nat := 118140960795 + 7931491 * 2 ^ 59
def prefixEnd_7931491 : Nat := 4983230072969 + 3 ^ 40 * 7931491 * 2
def baseEnd_7931491 : Nat := 4072667189809932738686243

theorem tailTrace_7931491 : CollatzResearch.WordTrace tailWord_7931491 prefixEnd_7931491 4072667189809932738686243 := by
  unfold tailWord_7931491
  simp only [CollatzResearch.WordTrace]
  refine ⟨289285242508570172663426327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192856828339046781775617551 289285242508570172663426327)
  ·
    refine ⟨433927863762855258995139491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289285242508570172663426327 433927863762855258995139491)
    ·
      refine ⟨650891795644282888492709237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433927863762855258995139491 650891795644282888492709237)
      ·
        refine ⟨61021105841651520796191491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 650891795644282888492709237 61021105841651520796191491)
        ·
          refine ⟨91531658762477281194287237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61021105841651520796191491 91531658762477281194287237)
          ·
            refine ⟨17162186017964490223928857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91531658762477281194287237 17162186017964490223928857)
            ·
              refine ⟨12871639513473367667946643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17162186017964490223928857 12871639513473367667946643)
              ·
                refine ⟨19307459270210051501919965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12871639513473367667946643 19307459270210051501919965)
                ·
                  refine ⟨7240297226328769313219987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19307459270210051501919965 7240297226328769313219987)
                  ·
                    refine ⟨10860445839493153969829981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7240297226328769313219987 10860445839493153969829981)
                    ·
                      refine ⟨4072667189809932738686243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10860445839493153969829981 4072667189809932738686243)
                      ·
                        rfl

theorem cell23_7931491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_7931491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931491 prefixEnd_7931491 := by exact prefixLift 7931491
  have htrace : WordTrace (prefixWord ++ tailWord_7931491) baseStart_7931491 baseEnd_7931491 := by
    simpa [prefixWord, tailWord_7931491, baseEnd_7931491] using wordTrace_append hprefix tailTrace_7931491
  have hstable : (prefixWord ++ tailWord_7931491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931491).length < 2 ^ (prefixWord ++ tailWord_7931491).sum := by decide
  have hdescent : baseEnd_7931491 < baseStart_7931491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931497 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 5, 1, 4]
def baseStart_7931497 : Nat := 118140960795 + 7931497 * 2 ^ 59
def prefixEnd_7931497 : Nat := 4983230072969 + 3 ^ 40 * 7931497 * 2
def baseEnd_7931497 : Nat := 4072670270693859715211215

theorem tailTrace_7931497 : CollatzResearch.WordTrace tailWord_7931497 prefixEnd_7931497 4072670270693859715211215 := by
  unfold tailWord_7931497
  simp only [CollatzResearch.WordTrace]
  refine ⟨289285461346548435688144745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192856974231032290458763163 289285461346548435688144745)
  ·
    refine ⟨216964096009911326766108559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289285461346548435688144745 216964096009911326766108559)
    ·
      refine ⟨325446144014866990149162839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216964096009911326766108559 325446144014866990149162839)
      ·
        refine ⟨488169216022300485223744259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325446144014866990149162839 488169216022300485223744259)
        ·
          refine ⟨732253824033450727835616389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488169216022300485223744259 732253824033450727835616389)
          ·
            refine ⟨137297592006272011469178073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 732253824033450727835616389 137297592006272011469178073)
            ·
              refine ⟨102973194004704008601883555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137297592006272011469178073 102973194004704008601883555)
              ·
                refine ⟨154459791007056012902825333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102973194004704008601883555 154459791007056012902825333)
                ·
                  refine ⟨14480605406911501209639875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154459791007056012902825333 14480605406911501209639875)
                  ·
                    refine ⟨21720908110367251814459813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14480605406911501209639875 21720908110367251814459813)
                    ·
                      refine ⟨4072670270693859715211215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21720908110367251814459813 4072670270693859715211215)
                      ·
                        rfl

theorem cell23_7931497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 1, 4].length) (baseStart_7931497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931497 prefixEnd_7931497 := by exact prefixLift 7931497
  have htrace : WordTrace (prefixWord ++ tailWord_7931497) baseStart_7931497 baseEnd_7931497 := by
    simpa [prefixWord, tailWord_7931497, baseEnd_7931497] using wordTrace_append hprefix tailTrace_7931497
  have hstable : (prefixWord ++ tailWord_7931497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931497).length < 2 ^ (prefixWord ++ tailWord_7931497).sum := by decide
  have hdescent : baseEnd_7931497 < baseStart_7931497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931534 : List Nat := [4, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_7931534 : Nat := 118140960795 + 7931534 * 2 ^ 59
def prefixEnd_7931534 : Nat := 4983230072969 + 3 ^ 40 * 7931534 * 2
def baseEnd_7931534 : Nat := 4072689269478076070448545

theorem tailTrace_7931534 : CollatzResearch.WordTrace tailWord_7931534 prefixEnd_7931534 4072689269478076070448545 := by
  unfold tailWord_7931534
  simp only [CollatzResearch.WordTrace]
  refine ⟨36160851355926798875905207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192857873898276260671494437 36160851355926798875905207)
  ·
    refine ⟨54241277033890198313857811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36160851355926798875905207 54241277033890198313857811)
    ·
      refine ⟨81361915550835297470786717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54241277033890198313857811 81361915550835297470786717)
      ·
        refine ⟨30510718331563236551545019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81361915550835297470786717 30510718331563236551545019)
        ·
          refine ⟨45766077497344854827317529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30510718331563236551545019 45766077497344854827317529)
          ·
            refine ⟨34324558123008641120488147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45766077497344854827317529 34324558123008641120488147)
            ·
              refine ⟨51486837184512961680732221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34324558123008641120488147 51486837184512961680732221)
              ·
                refine ⟨19307563944192360630274583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51486837184512961680732221 19307563944192360630274583)
                ·
                  refine ⟨28961345916288540945411875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19307563944192360630274583 28961345916288540945411875)
                  ·
                    refine ⟨43442018874432811418117813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28961345916288540945411875 43442018874432811418117813)
                    ·
                      refine ⟨4072689269478076070448545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43442018874432811418117813 4072689269478076070448545)
                      ·
                        rfl

theorem cell23_7931534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_7931534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931534 prefixEnd_7931534 := by exact prefixLift 7931534
  have htrace : WordTrace (prefixWord ++ tailWord_7931534) baseStart_7931534 baseEnd_7931534 := by
    simpa [prefixWord, tailWord_7931534, baseEnd_7931534] using wordTrace_append hprefix tailTrace_7931534
  have hstable : (prefixWord ++ tailWord_7931534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931534).length < 2 ^ (prefixWord ++ tailWord_7931534).sum := by decide
  have hdescent : baseEnd_7931534 < baseStart_7931534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931577 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 1, 4, 5]
def baseStart_7931577 : Nat := 118140960795 + 7931577 * 2 ^ 59
def prefixEnd_7931577 : Nat := 4983230072969 + 3 ^ 40 * 7931577 * 2
def baseEnd_7931577 : Nat := 4072711349146219402210847

theorem tailTrace_7931577 : CollatzResearch.WordTrace tailWord_7931577 prefixEnd_7931577 4072711349146219402210847 := by
  unfold tailWord_7931577
  simp only [CollatzResearch.WordTrace]
  refine ⟨289288379186258609351056985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192858919457505739567371323 289288379186258609351056985)
  ·
    refine ⟨216966284389693957013292739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289288379186258609351056985 216966284389693957013292739)
    ·
      refine ⟨325449426584540935519939109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216966284389693957013292739 325449426584540935519939109)
      ·
        refine ⟨61021767484601425409988583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325449426584540935519939109 61021767484601425409988583)
        ·
          refine ⟨91532651226902138114982875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61021767484601425409988583 91532651226902138114982875)
          ·
            refine ⟨137298976840353207172474313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91532651226902138114982875 137298976840353207172474313)
            ·
              refine ⟨102974232630264905379355735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137298976840353207172474313 102974232630264905379355735)
              ·
                refine ⟨154461348945397358069033603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102974232630264905379355735 154461348945397358069033603)
                ·
                  refine ⟨231692023418096037103550405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154461348945397358069033603 231692023418096037103550405)
                  ·
                    refine ⟨43442254390893006956915701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 231692023418096037103550405 43442254390893006956915701)
                    ·
                      refine ⟨4072711349146219402210847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43442254390893006956915701 4072711349146219402210847)
                      ·
                        rfl

theorem cell23_7931577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_7931577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931577 prefixEnd_7931577 := by exact prefixLift 7931577
  have htrace : WordTrace (prefixWord ++ tailWord_7931577) baseStart_7931577 baseEnd_7931577 := by
    simpa [prefixWord, tailWord_7931577, baseEnd_7931577] using wordTrace_append hprefix tailTrace_7931577
  have hstable : (prefixWord ++ tailWord_7931577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931577).length < 2 ^ (prefixWord ++ tailWord_7931577).sum := by decide
  have hdescent : baseEnd_7931577 < baseStart_7931577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931587 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 4]
def baseStart_7931587 : Nat := 118140960795 + 7931587 * 2 ^ 59
def prefixEnd_7931587 : Nat := 4983230072969 + 3 ^ 40 * 7931587 * 2
def baseEnd_7931587 : Nat := 4072716483952764363085801

theorem tailTrace_7931587 : CollatzResearch.WordTrace tailWord_7931587 prefixEnd_7931587 4072716483952764363085801 := by
  unfold tailWord_7931587
  simp only [CollatzResearch.WordTrace]
  refine ⟨289288743916222381058921015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192859162610814920705947343 289288743916222381058921015)
  ·
    refine ⟨433933115874333571588381523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289288743916222381058921015 433933115874333571588381523)
    ·
      refine ⟨650899673811500357382572285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433933115874333571588381523 650899673811500357382572285)
      ·
        refine ⟨244087377679312634018464607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 650899673811500357382572285 244087377679312634018464607)
        ·
          refine ⟨366131066518968951027696911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244087377679312634018464607 366131066518968951027696911)
          ·
            refine ⟨549196599778453426541545367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366131066518968951027696911 549196599778453426541545367)
            ·
              refine ⟨823794899667680139812318051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549196599778453426541545367 823794899667680139812318051)
              ·
                refine ⟨1235692349501520209718477077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823794899667680139812318051 1235692349501520209718477077)
                ·
                  refine ⟨57923078882883759830553613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1235692349501520209718477077 57923078882883759830553613)
                  ·
                    refine ⟨21721154581081409936457605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57923078882883759830553613 21721154581081409936457605)
                    ·
                      refine ⟨4072716483952764363085801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21721154581081409936457605 4072716483952764363085801)
                      ·
                        rfl

theorem cell23_7931587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_7931587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931587 prefixEnd_7931587 := by exact prefixLift 7931587
  have htrace : WordTrace (prefixWord ++ tailWord_7931587) baseStart_7931587 baseEnd_7931587 := by
    simpa [prefixWord, tailWord_7931587, baseEnd_7931587] using wordTrace_append hprefix tailTrace_7931587
  have hstable : (prefixWord ++ tailWord_7931587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931587).length < 2 ^ (prefixWord ++ tailWord_7931587).sum := by decide
  have hdescent : baseEnd_7931587 < baseStart_7931587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931598 : List Nat := [4, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3]
def baseStart_7931598 : Nat := 118140960795 + 7931598 * 2 ^ 59
def prefixEnd_7931598 : Nat := 4983230072969 + 3 ^ 40 * 7931598 * 2
def baseEnd_7931598 : Nat := 4072722132239963820048251

theorem tailTrace_7931598 : CollatzResearch.WordTrace tailWord_7931598 prefixEnd_7931598 4072722132239963820048251 := by
  unfold tailWord_7931598
  simp only [CollatzResearch.WordTrace]
  refine ⟨36161143139897816242196431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192859430079455019958380965 36161143139897816242196431)
  ·
    refine ⟨54241714709846724363294647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36161143139897816242196431 54241714709846724363294647)
    ·
      refine ⟨81362572064770086544941971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54241714709846724363294647 81362572064770086544941971)
      ·
        refine ⟨122043858097155129817412957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81362572064770086544941971 122043858097155129817412957)
        ·
          refine ⟨45766446786433173681529859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122043858097155129817412957 45766446786433173681529859)
          ·
            refine ⟨68649670179649760522294789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45766446786433173681529859 68649670179649760522294789)
            ·
              refine ⟨12871813158684330097930273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68649670179649760522294789 12871813158684330097930273)
              ·
                refine ⟨9653859869013247573447705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12871813158684330097930273 9653859869013247573447705)
                ·
                  refine ⟨7240394901759935680085779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9653859869013247573447705 7240394901759935680085779)
                  ·
                    refine ⟨10860592352639903520128669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7240394901759935680085779 10860592352639903520128669)
                    ·
                      refine ⟨4072722132239963820048251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10860592352639903520128669 4072722132239963820048251)
                      ·
                        rfl

theorem cell23_7931598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_7931598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931598 prefixEnd_7931598 := by exact prefixLift 7931598
  have htrace : WordTrace (prefixWord ++ tailWord_7931598) baseStart_7931598 baseEnd_7931598 := by
    simpa [prefixWord, tailWord_7931598, baseEnd_7931598] using wordTrace_append hprefix tailTrace_7931598
  have hstable : (prefixWord ++ tailWord_7931598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931598).length < 2 ^ (prefixWord ++ tailWord_7931598).sum := by decide
  have hdescent : baseEnd_7931598 < baseStart_7931598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931627 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 9]
def baseStart_7931627 : Nat := 118140960795 + 7931627 * 2 ^ 59
def prefixEnd_7931627 : Nat := 4983230072969 + 3 ^ 40 * 7931627 * 2
def baseEnd_7931627 : Nat := 452526335908771578509513

theorem tailTrace_7931627 : CollatzResearch.WordTrace tailWord_7931627 prefixEnd_7931627 452526335908771578509513 := by
  unfold tailWord_7931627
  simp only [CollatzResearch.WordTrace]
  refine ⟨289290202836077467890377135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192860135224051645260251423 289290202836077467890377135)
  ·
    refine ⟨433935304254116201835565703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289290202836077467890377135 433935304254116201835565703)
    ·
      refine ⟨650902956381174302753348555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433935304254116201835565703 650902956381174302753348555)
      ·
        refine ⟨976354434571761454130022833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650902956381174302753348555 976354434571761454130022833)
        ·
          refine ⟨732265825928821090597517125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 976354434571761454130022833 732265825928821090597517125)
          ·
            refine ⟨137299842361653954487034461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 732265825928821090597517125 137299842361653954487034461)
            ·
              refine ⟨51487440885620232932637923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137299842361653954487034461 51487440885620232932637923)
              ·
                refine ⟨77231161328430349398956885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51487440885620232932637923 77231161328430349398956885)
                ·
                  refine ⟨452526335908771578509513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77231161328430349398956885 452526335908771578509513)
                  ·
                    rfl

theorem cell23_7931627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 9].length) (baseStart_7931627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931627 prefixEnd_7931627 := by exact prefixLift 7931627
  have htrace : WordTrace (prefixWord ++ tailWord_7931627) baseStart_7931627 baseEnd_7931627 := by
    simpa [prefixWord, tailWord_7931627, baseEnd_7931627] using wordTrace_append hprefix tailTrace_7931627
  have hstable : (prefixWord ++ tailWord_7931627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931627).length < 2 ^ (prefixWord ++ tailWord_7931627).sum := by decide
  have hdescent : baseEnd_7931627 < baseStart_7931627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931634 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_7931634 : Nat := 118140960795 + 7931634 * 2 ^ 59
def prefixEnd_7931634 : Nat := 4983230072969 + 3 ^ 40 * 7931634 * 2
def baseEnd_7931634 : Nat := 4072740617543525679198085

theorem tailTrace_7931634 : CollatzResearch.WordTrace tailWord_7931634 prefixEnd_7931634 4072740617543525679198085 := by
  unfold tailWord_7931634
  simp only [CollatzResearch.WordTrace]
  refine ⟨72322614536763027021470489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192860305431368072057254637 72322614536763027021470489)
  ·
    refine ⟨54241960902572270266102867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72322614536763027021470489 54241960902572270266102867)
    ·
      refine ⟨81362941353858405399154301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54241960902572270266102867 81362941353858405399154301)
      ·
        refine ⟨30511103007696902024682863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81362941353858405399154301 30511103007696902024682863)
        ·
          refine ⟨45766654511545353037024295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30511103007696902024682863 45766654511545353037024295)
          ·
            refine ⟨68649981767318029555536443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45766654511545353037024295 68649981767318029555536443)
            ·
              refine ⟨102974972650977044333304665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68649981767318029555536443 102974972650977044333304665)
              ·
                refine ⟨77231229488232783249978499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102974972650977044333304665 77231229488232783249978499)
                ·
                  refine ⟨115846844232349174874967749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77231229488232783249978499 115846844232349174874967749)
                  ·
                    refine ⟨21721283293565470289056453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115846844232349174874967749 21721283293565470289056453)
                    ·
                      refine ⟨4072740617543525679198085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21721283293565470289056453 4072740617543525679198085)
                      ·
                        rfl

theorem cell23_7931634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_7931634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931634 prefixEnd_7931634 := by exact prefixLift 7931634
  have htrace : WordTrace (prefixWord ++ tailWord_7931634) baseStart_7931634 baseEnd_7931634 := by
    simpa [prefixWord, tailWord_7931634, baseEnd_7931634] using wordTrace_append hprefix tailTrace_7931634
  have hstable : (prefixWord ++ tailWord_7931634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931634).length < 2 ^ (prefixWord ++ tailWord_7931634).sum := by decide
  have hdescent : baseEnd_7931634 < baseStart_7931634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931638 : List Nat := [5, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2]
def baseStart_7931638 : Nat := 118140960795 + 7931638 * 2 ^ 59
def prefixEnd_7931638 : Nat := 4983230072969 + 3 ^ 40 * 7931638 * 2
def baseEnd_7931638 : Nat := 4072742671466143663548067

theorem tailTrace_7931638 : CollatzResearch.WordTrace tailWord_7931638 prefixEnd_7931638 4072742671466143663548067 := by
  unfold tailWord_7931638
  simp only [CollatzResearch.WordTrace]
  refine ⟨18080662752439851048064223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192860402692691744512685045 18080662752439851048064223)
  ·
    refine ⟨27120994128659776572096335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18080662752439851048064223 27120994128659776572096335)
    ·
      refine ⟨40681491192989664858144503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27120994128659776572096335 40681491192989664858144503)
      ·
        refine ⟨61022236789484497287216755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40681491192989664858144503 61022236789484497287216755)
        ·
          refine ⟨91533355184226745930825133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61022236789484497287216755 91533355184226745930825133)
          ·
            refine ⟨34325008194085029724059425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91533355184226745930825133 34325008194085029724059425)
            ·
              refine ⟨25743756145563772293044569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34325008194085029724059425 25743756145563772293044569)
              ·
                refine ⟨19307817109172829219783427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25743756145563772293044569 19307817109172829219783427)
                ·
                  refine ⟨28961725663759243829675141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19307817109172829219783427 28961725663759243829675141)
                  ·
                    refine ⟨5430323561954858218064089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28961725663759243829675141 5430323561954858218064089)
                    ·
                      refine ⟨4072742671466143663548067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5430323561954858218064089 4072742671466143663548067)
                      ·
                        rfl

theorem cell23_7931638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_7931638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931638 prefixEnd_7931638 := by exact prefixLift 7931638
  have htrace : WordTrace (prefixWord ++ tailWord_7931638) baseStart_7931638 baseEnd_7931638 := by
    simpa [prefixWord, tailWord_7931638, baseEnd_7931638] using wordTrace_append hprefix tailTrace_7931638
  have hstable : (prefixWord ++ tailWord_7931638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931638).length < 2 ^ (prefixWord ++ tailWord_7931638).sum := by decide
  have hdescent : baseEnd_7931638 < baseStart_7931638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931655 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 4, 2, 2]
def baseStart_7931655 : Nat := 118140960795 + 7931655 * 2 ^ 59
def prefixEnd_7931655 : Nat := 4983230072969 + 3 ^ 40 * 7931655 * 2
def baseEnd_7931655 : Nat := 4072751400637270097035489

theorem tailTrace_7931655 : CollatzResearch.WordTrace tailWord_7931655 prefixEnd_7931655 4072751400637270097035489 := by
  unfold tailWord_7931655
  simp only [CollatzResearch.WordTrace]
  refine ⟨289291224079976028672396419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192860816053317352448264279 289291224079976028672396419)
  ·
    refine ⟨433936836119964043008594629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289291224079976028672396419 433936836119964043008594629)
    ·
      refine ⟨81363156772493258064111493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 433936836119964043008594629 81363156772493258064111493)
      ·
        refine ⟨15255591894842485887020905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81363156772493258064111493 15255591894842485887020905)
        ·
          refine ⟨11441693921131864415265679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15255591894842485887020905 11441693921131864415265679)
          ·
            refine ⟨17162540881697796622898519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11441693921131864415265679 17162540881697796622898519)
            ·
              refine ⟨25743811322546694934347779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17162540881697796622898519 25743811322546694934347779)
              ·
                refine ⟨38615716983820042401521669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25743811322546694934347779 38615716983820042401521669)
                ·
                  refine ⟨7240446934466257950285313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38615716983820042401521669 7240446934466257950285313)
                  ·
                    refine ⟨5430335200849693462713985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7240446934466257950285313 5430335200849693462713985)
                    ·
                      refine ⟨4072751400637270097035489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5430335200849693462713985 4072751400637270097035489)
                      ·
                        rfl

theorem cell23_7931655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_7931655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931655 prefixEnd_7931655 := by exact prefixLift 7931655
  have htrace : WordTrace (prefixWord ++ tailWord_7931655) baseStart_7931655 baseEnd_7931655 := by
    simpa [prefixWord, tailWord_7931655, baseEnd_7931655] using wordTrace_append hprefix tailTrace_7931655
  have hstable : (prefixWord ++ tailWord_7931655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931655).length < 2 ^ (prefixWord ++ tailWord_7931655).sum := by decide
  have hdescent : baseEnd_7931655 < baseStart_7931655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931671 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 3]
def baseStart_7931671 : Nat := 118140960795 + 7931671 * 2 ^ 59
def prefixEnd_7931671 : Nat := 4983230072969 + 3 ^ 40 * 7931671 * 2
def baseEnd_7931671 : Nat := 4072759616327742034435415

theorem tailTrace_7931671 : CollatzResearch.WordTrace tailWord_7931671 prefixEnd_7931671 4072759616327742034435415 := by
  unfold tailWord_7931671
  simp only [CollatzResearch.WordTrace]
  refine ⟨289291807647918063404978867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192861205098612042269985911 289291807647918063404978867)
  ·
    refine ⟨433937711471877095107468301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289291807647918063404978867 433937711471877095107468301)
    ·
      refine ⟨162726641801953910665300613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433937711471877095107468301 162726641801953910665300613)
      ·
        refine ⟨30511245337866358249743865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162726641801953910665300613 30511245337866358249743865)
        ·
          refine ⟨22883434003399768687307899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30511245337866358249743865 22883434003399768687307899)
          ·
            refine ⟨34325151005099653030961849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22883434003399768687307899 34325151005099653030961849)
            ·
              refine ⟨25743863253824739773221387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34325151005099653030961849 25743863253824739773221387)
              ·
                refine ⟨38615794880737109659832081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25743863253824739773221387 38615794880737109659832081)
                ·
                  refine ⟨28961846160552832244874061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38615794880737109659832081 28961846160552832244874061)
                  ·
                    refine ⟨10860692310207312091827773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28961846160552832244874061 10860692310207312091827773)
                    ·
                      refine ⟨4072759616327742034435415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10860692310207312091827773 4072759616327742034435415)
                      ·
                        rfl

theorem cell23_7931671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_7931671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931671 prefixEnd_7931671 := by exact prefixLift 7931671
  have htrace : WordTrace (prefixWord ++ tailWord_7931671) baseStart_7931671 baseEnd_7931671 := by
    simpa [prefixWord, tailWord_7931671, baseEnd_7931671] using wordTrace_append hprefix tailTrace_7931671
  have hstable : (prefixWord ++ tailWord_7931671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931671).length < 2 ^ (prefixWord ++ tailWord_7931671).sum := by decide
  have hdescent : baseEnd_7931671 < baseStart_7931671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931674 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 1, 7]
def baseStart_7931674 : Nat := 118140960795 + 7931674 * 2 ^ 59
def prefixEnd_7931674 : Nat := 4983230072969 + 3 ^ 40 * 7931674 * 2
def baseEnd_7931674 : Nat := 1357587052256568507565967

theorem tailTrace_7931674 : CollatzResearch.WordTrace tailWord_7931674 prefixEnd_7931674 1357587052256568507565967 := by
  unfold tailWord_7931674
  simp only [CollatzResearch.WordTrace]
  refine ⟨72322979266726798729334519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192861278044604796611558717 72322979266726798729334519)
  ·
    refine ⟨108484468900090198094001779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72322979266726798729334519 108484468900090198094001779)
    ·
      refine ⟨162726703350135297141002669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108484468900090198094001779 162726703350135297141002669)
      ·
        refine ⟨61022513756300736427876001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162726703350135297141002669 61022513756300736427876001)
        ·
          refine ⟨45766885317225552320907001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61022513756300736427876001 45766885317225552320907001)
          ·
            refine ⟨34325163987919164240680251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45766885317225552320907001 34325163987919164240680251)
            ·
              refine ⟨51487745981878746361020377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34325163987919164240680251 51487745981878746361020377)
              ·
                refine ⟨38615809486409059770765283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51487745981878746361020377 38615809486409059770765283)
                ·
                  refine ⟨57923714229613589656147925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38615809486409059770765283 57923714229613589656147925)
                  ·
                    refine ⟨1357587052256568507565967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57923714229613589656147925 1357587052256568507565967)
                    ·
                      rfl

theorem cell23_7931674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_7931674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931674 prefixEnd_7931674 := by exact prefixLift 7931674
  have htrace : WordTrace (prefixWord ++ tailWord_7931674) baseStart_7931674 baseEnd_7931674 := by
    simpa [prefixWord, tailWord_7931674, baseEnd_7931674] using wordTrace_append hprefix tailTrace_7931674
  have hstable : (prefixWord ++ tailWord_7931674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931674).length < 2 ^ (prefixWord ++ tailWord_7931674).sum := by decide
  have hdescent : baseEnd_7931674 < baseStart_7931674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931718 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_7931718 : Nat := 118140960795 + 7931718 * 2 ^ 59
def prefixEnd_7931718 : Nat := 4983230072969 + 3 ^ 40 * 7931718 * 2
def baseEnd_7931718 : Nat := 4072783749918503350547699

theorem tailTrace_7931718 : CollatzResearch.WordTrace tailWord_7931718 prefixEnd_7931718 4072783749918503350547699 := by
  unfold tailWord_7931718
  simp only [CollatzResearch.WordTrace]
  refine ⟨9040422558710868450998119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 192862347919165193621293205 9040422558710868450998119)
  ·
    refine ⟨13560633838066302676497179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9040422558710868450998119 13560633838066302676497179)
    ·
      refine ⟨20340950757099454014745769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13560633838066302676497179 20340950757099454014745769)
      ·
        refine ⟨15255713067824590511059327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20340950757099454014745769 15255713067824590511059327)
        ·
          refine ⟨22883569601736885766588991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15255713067824590511059327 22883569601736885766588991)
          ·
            refine ⟨34325354402605328649883487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22883569601736885766588991 34325354402605328649883487)
            ·
              refine ⟨51488031603907992974825231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34325354402605328649883487 51488031603907992974825231)
              ·
                refine ⟨77232047405861989462237847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51488031603907992974825231 77232047405861989462237847)
                ·
                  refine ⟨115848071108792984193356771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77232047405861989462237847 115848071108792984193356771)
                  ·
                    refine ⟨173772106663189476290035157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115848071108792984193356771 173772106663189476290035157)
                    ·
                      refine ⟨4072783749918503350547699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173772106663189476290035157 4072783749918503350547699)
                      ·
                        rfl

theorem cell23_7931718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_7931718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931718 prefixEnd_7931718 := by exact prefixLift 7931718
  have htrace : WordTrace (prefixWord ++ tailWord_7931718) baseStart_7931718 baseEnd_7931718 := by
    simpa [prefixWord, tailWord_7931718, baseEnd_7931718] using wordTrace_append hprefix tailTrace_7931718
  have hstable : (prefixWord ++ tailWord_7931718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931718).length < 2 ^ (prefixWord ++ tailWord_7931718).sum := by decide
  have hdescent : baseEnd_7931718 < baseStart_7931718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931771 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 3, 5, 2]
def baseStart_7931771 : Nat := 118140960795 + 7931771 * 2 ^ 59
def prefixEnd_7931771 : Nat := 4983230072969 + 3 ^ 40 * 7931771 * 2
def baseEnd_7931771 : Nat := 4072810964393191643184955

theorem tailTrace_7931771 : CollatzResearch.WordTrace tailWord_7931771 prefixEnd_7931771 4072810964393191643184955 := by
  unfold tailWord_7931771
  simp only [CollatzResearch.WordTrace]
  refine ⟨289295454947555780483619167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192863636631703853655746111 289295454947555780483619167)
  ·
    refine ⟨433943182421333670725428751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289295454947555780483619167 433943182421333670725428751)
    ·
      refine ⟨650914773632000506088143127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433943182421333670725428751 650914773632000506088143127)
      ·
        refine ⟨976372160448000759132214691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650914773632000506088143127 976372160448000759132214691)
        ·
          refine ⟨1464558240672001138698322037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976372160448000759132214691 1464558240672001138698322037)
          ·
            refine ⟨137302335063000106752967691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1464558240672001138698322037 137302335063000106752967691)
            ·
              refine ⟨205953502594500160129451537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137302335063000106752967691 205953502594500160129451537)
              ·
                refine ⟨154465126945875120097088653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205953502594500160129451537 154465126945875120097088653)
                ·
                  refine ⟨57924422604703170036408245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154465126945875120097088653 57924422604703170036408245)
                  ·
                    refine ⟨5430414619190922190913273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57924422604703170036408245 5430414619190922190913273)
                    ·
                      refine ⟨4072810964393191643184955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5430414619190922190913273 4072810964393191643184955)
                      ·
                        rfl

theorem cell23_7931771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 5, 2].length) (baseStart_7931771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931771 prefixEnd_7931771 := by exact prefixLift 7931771
  have htrace : WordTrace (prefixWord ++ tailWord_7931771) baseStart_7931771 baseEnd_7931771 := by
    simpa [prefixWord, tailWord_7931771, baseEnd_7931771] using wordTrace_append hprefix tailTrace_7931771
  have hstable : (prefixWord ++ tailWord_7931771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931771).length < 2 ^ (prefixWord ++ tailWord_7931771).sum := by decide
  have hdescent : baseEnd_7931771 < baseStart_7931771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931801 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 3, 1, 4]
def baseStart_7931801 : Nat := 118140960795 + 7931801 * 2 ^ 59
def prefixEnd_7931801 : Nat := 4983230072969 + 3 ^ 40 * 7931801 * 2
def baseEnd_7931801 : Nat := 4072826368812826525809817

theorem tailTrace_7931801 : CollatzResearch.WordTrace tailWord_7931801 prefixEnd_7931801 4072826368812826525809817 := by
  unfold tailWord_7931801
  simp only [CollatzResearch.WordTrace]
  refine ⟨289296549137447095607211257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192864366091631397071474171 289296549137447095607211257)
  ·
    refine ⟨216972411853085321705408443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289296549137447095607211257 216972411853085321705408443)
    ·
      refine ⟨325458617779627982558112665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216972411853085321705408443 325458617779627982558112665)
      ·
        refine ⟨244093963334720986918584499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325458617779627982558112665 244093963334720986918584499)
        ·
          refine ⟨366140945002081480377876749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244093963334720986918584499 366140945002081480377876749)
          ·
            refine ⟨137302854375780555141703781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366140945002081480377876749 137302854375780555141703781)
            ·
              refine ⟨25744285195458854089069459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137302854375780555141703781 25744285195458854089069459)
              ·
                refine ⟨38616427793188281133604189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25744285195458854089069459 38616427793188281133604189)
                ·
                  refine ⟨14481160422445605425101571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38616427793188281133604189 14481160422445605425101571)
                  ·
                    refine ⟨21721740633668408137652357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14481160422445605425101571 21721740633668408137652357)
                    ·
                      refine ⟨4072826368812826525809817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21721740633668408137652357 4072826368812826525809817)
                      ·
                        rfl

theorem cell23_7931801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_7931801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931801 prefixEnd_7931801 := by exact prefixLift 7931801
  have htrace : WordTrace (prefixWord ++ tailWord_7931801) baseStart_7931801 baseEnd_7931801 := by
    simpa [prefixWord, tailWord_7931801, baseEnd_7931801] using wordTrace_append hprefix tailTrace_7931801
  have hstable : (prefixWord ++ tailWord_7931801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931801).length < 2 ^ (prefixWord ++ tailWord_7931801).sum := by decide
  have hdescent : baseEnd_7931801 < baseStart_7931801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931805 : List Nat := [1, 4, 2, 1, 2, 2, 3, 1, 2, 3, 2]
def baseStart_7931805 : Nat := 118140960795 + 7931805 * 2 ^ 59
def prefixEnd_7931805 : Nat := 4983230072969 + 3 ^ 40 * 7931805 * 2
def baseEnd_7931805 : Nat := 4072828422735444510159799

theorem tailTrace_7931805 : CollatzResearch.WordTrace tailWord_7931805 prefixEnd_7931805 4072828422735444510159799 := by
  unfold tailWord_7931805
  simp only [CollatzResearch.WordTrace]
  refine ⟨289296695029432604290356869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192864463352955069526904579 289296695029432604290356869)
  ·
    refine ⟨54243130318018613304441913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289296695029432604290356869 54243130318018613304441913)
    ·
      refine ⟨40682347738513959978331435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54243130318018613304441913 40682347738513959978331435)
      ·
        refine ⟨61023521607770939967497153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40682347738513959978331435 61023521607770939967497153)
        ·
          refine ⟨45767641205828204975622865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61023521607770939967497153 45767641205828204975622865)
          ·
            refine ⟨34325730904371153731717149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45767641205828204975622865 34325730904371153731717149)
            ·
              refine ⟨12872149089139182649393931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34325730904371153731717149 12872149089139182649393931)
              ·
                refine ⟨19308223633708773974090897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12872149089139182649393931 19308223633708773974090897)
                ·
                  refine ⟨14481167725281580480568173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19308223633708773974090897 14481167725281580480568173)
                  ·
                    refine ⟨5430437896980592680213065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14481167725281580480568173 5430437896980592680213065)
                    ·
                      refine ⟨4072828422735444510159799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5430437896980592680213065 4072828422735444510159799)
                      ·
                        rfl

theorem cell23_7931805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_7931805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931805 prefixEnd_7931805 := by exact prefixLift 7931805
  have htrace : WordTrace (prefixWord ++ tailWord_7931805) baseStart_7931805 baseEnd_7931805 := by
    simpa [prefixWord, tailWord_7931805, baseEnd_7931805] using wordTrace_append hprefix tailTrace_7931805
  have hstable : (prefixWord ++ tailWord_7931805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931805).length < 2 ^ (prefixWord ++ tailWord_7931805).sum := by decide
  have hdescent : baseEnd_7931805 < baseStart_7931805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931811 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 4, 4]
def baseStart_7931811 : Nat := 118140960795 + 7931811 * 2 ^ 59
def prefixEnd_7931811 : Nat := 4983230072969 + 3 ^ 40 * 7931811 * 2
def baseEnd_7931811 : Nat := 1357610501206457162228257

theorem tailTrace_7931811 : CollatzResearch.WordTrace tailWord_7931811 prefixEnd_7931811 1357610501206457162228257 := by
  unfold tailWord_7931811
  simp only [CollatzResearch.WordTrace]
  refine ⟨289296913867410867315075287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192864609244940578210050191 289296913867410867315075287)
  ·
    refine ⟨433945370801116300972612931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289296913867410867315075287 433945370801116300972612931)
    ·
      refine ⟨650918056201674451458919397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433945370801116300972612931 650918056201674451458919397)
      ·
        refine ⟨122047135537813959648547387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 650918056201674451458919397 122047135537813959648547387)
        ·
          refine ⟨183070703306720939472821081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122047135537813959648547387 183070703306720939472821081)
          ·
            refine ⟨137303027480040704604615811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183070703306720939472821081 137303027480040704604615811)
            ·
              refine ⟨205954541220061056906923717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137303027480040704604615811 205954541220061056906923717)
              ·
                refine ⟨38616476478761448170048197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205954541220061056906923717 38616476478761448170048197)
                ·
                  refine ⟨7240589339767771531884037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38616476478761448170048197 7240589339767771531884037)
                  ·
                    refine ⟨1357610501206457162228257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7240589339767771531884037 1357610501206457162228257)
                    ·
                      rfl

theorem cell23_7931811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 4].length) (baseStart_7931811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931811 prefixEnd_7931811 := by exact prefixLift 7931811
  have htrace : WordTrace (prefixWord ++ tailWord_7931811) baseStart_7931811 baseEnd_7931811 := by
    simpa [prefixWord, tailWord_7931811, baseEnd_7931811] using wordTrace_append hprefix tailTrace_7931811
  have hstable : (prefixWord ++ tailWord_7931811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931811).length < 2 ^ (prefixWord ++ tailWord_7931811).sum := by decide
  have hdescent : baseEnd_7931811 < baseStart_7931811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931812 : List Nat := [2, 3, 1, 2, 1, 4, 2, 3, 1, 1, 3]
def baseStart_7931812 : Nat := 118140960795 + 7931812 * 2 ^ 59
def prefixEnd_7931812 : Nat := 4983230072969 + 3 ^ 40 * 7931812 * 2
def baseEnd_7931812 : Nat := 4072832017100025982772267

theorem tailTrace_7931812 : CollatzResearch.WordTrace tailWord_7931812 prefixEnd_7931812 4072832017100025982772267 := by
  unfold tailWord_7931812
  simp only [CollatzResearch.WordTrace]
  refine ⟨144648475170203622242930845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192864633560271496323907793 144648475170203622242930845)
  ·
    refine ⟨54243178188826358341099067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144648475170203622242930845 54243178188826358341099067)
    ·
      refine ⟨81364767283239537511648601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54243178188826358341099067 81364767283239537511648601)
      ·
        refine ⟨61023575462429653133736451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81364767283239537511648601 61023575462429653133736451)
        ·
          refine ⟨91535363193644479700604677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61023575462429653133736451 91535363193644479700604677)
          ·
            refine ⟨17162880598808339943863377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91535363193644479700604677 17162880598808339943863377)
            ·
              refine ⟨12872160449106254957897533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17162880598808339943863377 12872160449106254957897533)
              ·
                refine ⟨4827060168414845609211575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12872160449106254957897533 4827060168414845609211575)
                ·
                  refine ⟨7240590252622268413817363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4827060168414845609211575 7240590252622268413817363)
                  ·
                    refine ⟨10860885378933402620726045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7240590252622268413817363 10860885378933402620726045)
                    ·
                      refine ⟨4072832017100025982772267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10860885378933402620726045 4072832017100025982772267)
                      ·
                        rfl

theorem cell23_7931812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_7931812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931812 prefixEnd_7931812 := by exact prefixLift 7931812
  have htrace : WordTrace (prefixWord ++ tailWord_7931812) baseStart_7931812 baseEnd_7931812 := by
    simpa [prefixWord, tailWord_7931812, baseEnd_7931812] using wordTrace_append hprefix tailTrace_7931812
  have hstable : (prefixWord ++ tailWord_7931812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931812).length < 2 ^ (prefixWord ++ tailWord_7931812).sum := by decide
  have hdescent : baseEnd_7931812 < baseStart_7931812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931815 : List Nat := [1, 1, 6, 1, 2, 1, 4, 1, 1, 5]
def baseStart_7931815 : Nat := 118140960795 + 7931815 * 2 ^ 59
def prefixEnd_7931815 : Nat := 4983230072969 + 3 ^ 40 * 7931815 * 2
def baseEnd_7931815 : Nat := 1357611185847329823678251

theorem tailTrace_7931815 : CollatzResearch.WordTrace tailWord_7931815 prefixEnd_7931815 1357611185847329823678251 := by
  unfold tailWord_7931815
  simp only [CollatzResearch.WordTrace]
  refine ⟨289297059759396375998220899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192864706506264250665480599 289297059759396375998220899)
  ·
    refine ⟨433945589639094563997331349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289297059759396375998220899 433945589639094563997331349)
    ·
      refine ⟨20341199514332557687374907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 433945589639094563997331349 20341199514332557687374907)
      ·
        refine ⟨30511799271498836531062361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20341199514332557687374907 30511799271498836531062361)
        ·
          refine ⟨22883849453624127398296771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30511799271498836531062361 22883849453624127398296771)
          ·
            refine ⟨34325774180436191097445157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22883849453624127398296771 34325774180436191097445157)
            ·
              refine ⟨6436082658831785830770967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34325774180436191097445157 6436082658831785830770967)
              ·
                refine ⟨9654123988247678746156451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6436082658831785830770967 9654123988247678746156451)
                ·
                  refine ⟨14481185982371518119234677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9654123988247678746156451 14481185982371518119234677)
                  ·
                    refine ⟨1357611185847329823678251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14481185982371518119234677 1357611185847329823678251)
                    ·
                      rfl

theorem cell23_7931815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_7931815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931815 prefixEnd_7931815 := by exact prefixLift 7931815
  have htrace : WordTrace (prefixWord ++ tailWord_7931815) baseStart_7931815 baseEnd_7931815 := by
    simpa [prefixWord, tailWord_7931815, baseEnd_7931815] using wordTrace_append hprefix tailTrace_7931815
  have hstable : (prefixWord ++ tailWord_7931815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931815).length < 2 ^ (prefixWord ++ tailWord_7931815).sum := by decide
  have hdescent : baseEnd_7931815 < baseStart_7931815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931838 : List Nat := [4, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_7931838 : Nat := 118140960795 + 7931838 * 2 ^ 59
def prefixEnd_7931838 : Nat := 4983230072969 + 3 ^ 40 * 7931838 * 2
def baseEnd_7931838 : Nat := 4072845367597042881047147

theorem tailTrace_7931838 : CollatzResearch.WordTrace tailWord_7931838 prefixEnd_7931838 4072845367597042881047147 := by
  unfold tailWord_7931838
  simp only [CollatzResearch.WordTrace]
  refine ⟨36162237329789131365788521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192865265758875367284205445 36162237329789131365788521)
  ·
    refine ⟨27121677997341848524341391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36162237329789131365788521 27121677997341848524341391)
    ·
      refine ⟨40682516996012772786512087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27121677997341848524341391 40682516996012772786512087)
      ·
        refine ⟨61023775494019159179768131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40682516996012772786512087 61023775494019159179768131)
        ·
          refine ⟨91535663241028738769652197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61023775494019159179768131 91535663241028738769652197)
          ·
            refine ⟨17162936857692888519309787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91535663241028738769652197 17162936857692888519309787)
            ·
              refine ⟨25744405286539332778964681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17162936857692888519309787 25744405286539332778964681)
              ·
                refine ⟨19308303964904499584223511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25744405286539332778964681 19308303964904499584223511)
                ·
                  refine ⟨28962455947356749376335267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19308303964904499584223511 28962455947356749376335267)
                  ·
                    refine ⟨43443683921035124064502901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28962455947356749376335267 43443683921035124064502901)
                    ·
                      refine ⟨4072845367597042881047147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43443683921035124064502901 4072845367597042881047147)
                      ·
                        rfl

theorem cell23_7931838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_7931838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931838 prefixEnd_7931838 := by exact prefixLift 7931838
  have htrace : WordTrace (prefixWord ++ tailWord_7931838) baseStart_7931838 baseEnd_7931838 := by
    simpa [prefixWord, tailWord_7931838, baseEnd_7931838] using wordTrace_append hprefix tailTrace_7931838
  have hstable : (prefixWord ++ tailWord_7931838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931838).length < 2 ^ (prefixWord ++ tailWord_7931838).sum := by decide
  have hdescent : baseEnd_7931838 < baseStart_7931838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931848 : List Nat := [2, 1, 3, 1, 4, 1, 3, 1, 1, 2, 4]
def baseStart_7931848 : Nat := 118140960795 + 7931848 * 2 ^ 59
def prefixEnd_7931848 : Nat := 4983230072969 + 3 ^ 40 * 7931848 * 2
def baseEnd_7931848 : Nat := 4072850502403587841922101

theorem tailTrace_7931848 : CollatzResearch.WordTrace tailWord_7931848 prefixEnd_7931848 4072850502403587841922101 := by
  unfold tailWord_7931848
  simp only [CollatzResearch.WordTrace]
  refine ⟨144649131684138411317086099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192865508912184548422781465 144649131684138411317086099)
  ·
    refine ⟨216973697526207616975629149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144649131684138411317086099 216973697526207616975629149)
    ·
      refine ⟨81365136572327856365860931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216973697526207616975629149 81365136572327856365860931)
      ·
        refine ⟨122047704858491784548791397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81365136572327856365860931 122047704858491784548791397)
        ·
          refine ⟨22883944660967209602898387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122047704858491784548791397 22883944660967209602898387)
          ·
            refine ⟨34325916991450814404347581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22883944660967209602898387 34325916991450814404347581)
            ·
              refine ⟨12872218871794055401630343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34325916991450814404347581 12872218871794055401630343)
              ·
                refine ⟨19308328307691083102445515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12872218871794055401630343 19308328307691083102445515)
                ·
                  refine ⟨28962492461536624653668273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19308328307691083102445515 28962492461536624653668273)
                  ·
                    refine ⟨21721869346152468490251205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28962492461536624653668273 21721869346152468490251205)
                    ·
                      refine ⟨4072850502403587841922101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21721869346152468490251205 4072850502403587841922101)
                      ·
                        rfl

theorem cell23_7931848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_7931848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931848 prefixEnd_7931848 := by exact prefixLift 7931848
  have htrace : WordTrace (prefixWord ++ tailWord_7931848) baseStart_7931848 baseEnd_7931848 := by
    simpa [prefixWord, tailWord_7931848, baseEnd_7931848] using wordTrace_append hprefix tailTrace_7931848
  have hstable : (prefixWord ++ tailWord_7931848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931848).length < 2 ^ (prefixWord ++ tailWord_7931848).sum := by decide
  have hdescent : baseEnd_7931848 < baseStart_7931848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931858 : List Nat := [3, 2, 2, 3, 2, 1, 1, 9]
def baseStart_7931858 : Nat := 118140960795 + 7931858 * 2 ^ 59
def prefixEnd_7931858 : Nat := 4983230072969 + 3 ^ 40 * 7931858 * 2
def baseEnd_7931858 : Nat := 150846505081856770473965

theorem tailTrace_7931858 : CollatzResearch.WordTrace tailWord_7931858 prefixEnd_7931858 150846505081856770473965 := by
  unfold tailWord_7931858
  simp only [CollatzResearch.WordTrace]
  refine ⟨72324657024560148585509057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192865752065493729561357485 72324657024560148585509057)
  ·
    refine ⟨54243492768420111439131793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72324657024560148585509057 54243492768420111439131793)
    ·
      refine ⟨40682619576315083579348845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54243492768420111439131793 40682619576315083579348845)
      ·
        refine ⟨15255982341118156342255817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40682619576315083579348845 15255982341118156342255817)
        ·
          refine ⟨11441986755838617256691863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15255982341118156342255817 11441986755838617256691863)
          ·
            refine ⟨17162980133757925885037795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11441986755838617256691863 17162980133757925885037795)
            ·
              refine ⟨25744470200636888827556693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17162980133757925885037795 25744470200636888827556693)
              ·
                refine ⟨150846505081856770473965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25744470200636888827556693 150846505081856770473965)
                ·
                  rfl

theorem cell23_7931858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 9].length) (baseStart_7931858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931858 prefixEnd_7931858 := by exact prefixLift 7931858
  have htrace : WordTrace (prefixWord ++ tailWord_7931858) baseStart_7931858 baseEnd_7931858 := by
    simpa [prefixWord, tailWord_7931858, baseEnd_7931858] using wordTrace_append hprefix tailTrace_7931858
  have hstable : (prefixWord ++ tailWord_7931858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931858).length < 2 ^ (prefixWord ++ tailWord_7931858).sum := by decide
  have hdescent : baseEnd_7931858 < baseStart_7931858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931886 : List Nat := [4, 1, 2, 1, 3, 2, 3, 2, 1, 2, 2]
def baseStart_7931886 : Nat := 118140960795 + 7931886 * 2 ^ 59
def prefixEnd_7931886 : Nat := 4983230072969 + 3 ^ 40 * 7931886 * 2
def baseEnd_7931886 : Nat := 4072870014668458693246927

theorem tailTrace_7931886 : CollatzResearch.WordTrace tailWord_7931886 prefixEnd_7931886 4072870014668458693246927 := by
  unfold tailWord_7931886
  simp only [CollatzResearch.WordTrace]
  refine ⟨36162456167767394390506939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192866432894759436749370341 36162456167767394390506939)
  ·
    refine ⟨54243684251651091585760409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36162456167767394390506939 54243684251651091585760409)
    ·
      refine ⟨40682763188738318689320307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54243684251651091585760409 40682763188738318689320307)
      ·
        refine ⟨61024144783107478033980461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40682763188738318689320307 61024144783107478033980461)
        ·
          refine ⟨22884054293665304262742673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61024144783107478033980461 22884054293665304262742673)
          ·
            refine ⟨17163040720248978197057005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22884054293665304262742673 17163040720248978197057005)
            ·
              refine ⟨6436140270093366823896377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17163040720248978197057005 6436140270093366823896377)
              ·
                refine ⟨4827105202570025117922283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6436140270093366823896377 4827105202570025117922283)
                ·
                  refine ⟨7240657803855037676883425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4827105202570025117922283 7240657803855037676883425)
                  ·
                    refine ⟨5430493352891278257662569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7240657803855037676883425 5430493352891278257662569)
                    ·
                      refine ⟨4072870014668458693246927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5430493352891278257662569 4072870014668458693246927)
                      ·
                        rfl

theorem cell23_7931886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_7931886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931886 prefixEnd_7931886 := by exact prefixLift 7931886
  have htrace : WordTrace (prefixWord ++ tailWord_7931886) baseStart_7931886 baseEnd_7931886 := by
    simpa [prefixWord, tailWord_7931886, baseEnd_7931886] using wordTrace_append hprefix tailTrace_7931886
  have hstable : (prefixWord ++ tailWord_7931886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931886).length < 2 ^ (prefixWord ++ tailWord_7931886).sum := by decide
  have hdescent : baseEnd_7931886 < baseStart_7931886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931901 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 2, 6]
def baseStart_7931901 : Nat := 118140960795 + 7931901 * 2 ^ 59
def prefixEnd_7931901 : Nat := 4983230072969 + 3 ^ 40 * 7931901 * 2
def baseEnd_7931901 : Nat := 1357625905626092044853119

theorem tailTrace_7931901 : CollatzResearch.WordTrace tailWord_7931901 prefixEnd_7931901 1357625905626092044853119 := by
  unfold tailWord_7931901
  simp only [CollatzResearch.WordTrace]
  refine ⟨289300196437084812685851557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192866797624723208457234371 289300196437084812685851557)
  ·
    refine ⟨54243786831953402378597167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289300196437084812685851557 54243786831953402378597167)
    ·
      refine ⟨81365680247930103567895751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54243786831953402378597167 81365680247930103567895751)
      ·
        refine ⟨122048520371895155351843627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81365680247930103567895751 122048520371895155351843627)
        ·
          refine ⟨183072780557842733027765441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122048520371895155351843627 183072780557842733027765441)
          ·
            refine ⟨137304585418382049770824081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183072780557842733027765441 137304585418382049770824081)
            ·
              refine ⟨102978439063786537328118061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137304585418382049770824081 102978439063786537328118061)
              ·
                refine ⟨38616914648919951498044273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102978439063786537328118061 38616914648919951498044273)
                ·
                  refine ⟨28962685986689963623533205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38616914648919951498044273 28962685986689963623533205)
                  ·
                    refine ⟨1357625905626092044853119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28962685986689963623533205 1357625905626092044853119)
                    ·
                      rfl

theorem cell23_7931901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_7931901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931901 prefixEnd_7931901 := by exact prefixLift 7931901
  have htrace : WordTrace (prefixWord ++ tailWord_7931901) baseStart_7931901 baseEnd_7931901 := by
    simpa [prefixWord, tailWord_7931901, baseEnd_7931901] using wordTrace_append hprefix tailTrace_7931901
  have hstable : (prefixWord ++ tailWord_7931901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931901).length < 2 ^ (prefixWord ++ tailWord_7931901).sum := by decide
  have hdescent : baseEnd_7931901 < baseStart_7931901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931921 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 4]
def baseStart_7931921 : Nat := 118140960795 + 7931921 * 2 ^ 59
def prefixEnd_7931921 : Nat := 4983230072969 + 3 ^ 40 * 7931921 * 2
def baseEnd_7931921 : Nat := 4072887986491366056309265

theorem tailTrace_7931921 : CollatzResearch.WordTrace tailWord_7931921 prefixEnd_7931921 4072887986491366056309265 := by
  unfold tailWord_7931921
  simp only [CollatzResearch.WordTrace]
  refine ⟨289300925897012356101579617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192867283931341570734386411 289300925897012356101579617)
  ·
    refine ⟨216975694422759267076184713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289300925897012356101579617 216975694422759267076184713)
    ·
      refine ⟨162731770817069450307138535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216975694422759267076184713 162731770817069450307138535)
      ·
        refine ⟨244097656225604175460707803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162731770817069450307138535 244097656225604175460707803)
        ·
          refine ⟨366146484338406263191061705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244097656225604175460707803 366146484338406263191061705)
          ·
            refine ⟨274609863253804697393296279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366146484338406263191061705 274609863253804697393296279)
            ·
              refine ⟨411914794880707046089944419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274609863253804697393296279 411914794880707046089944419)
              ·
                refine ⟨617872192321060569134916629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411914794880707046089944419 617872192321060569134916629)
                ·
                  refine ⟨28962759015049714178199217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 617872192321060569134916629 28962759015049714178199217)
                  ·
                    refine ⟨21722069261287285633649413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28962759015049714178199217 21722069261287285633649413)
                    ·
                      refine ⟨4072887986491366056309265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21722069261287285633649413 4072887986491366056309265)
                      ·
                        rfl

theorem cell23_7931921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_7931921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931921 prefixEnd_7931921 := by exact prefixLift 7931921
  have htrace : WordTrace (prefixWord ++ tailWord_7931921) baseStart_7931921 baseEnd_7931921 := by
    simpa [prefixWord, tailWord_7931921, baseEnd_7931921] using wordTrace_append hprefix tailTrace_7931921
  have hstable : (prefixWord ++ tailWord_7931921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931921).length < 2 ^ (prefixWord ++ tailWord_7931921).sum := by decide
  have hdescent : baseEnd_7931921 < baseStart_7931921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931938 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_7931938 : Nat := 118140960795 + 7931938 * 2 ^ 59
def prefixEnd_7931938 : Nat := 4983230072969 + 3 ^ 40 * 7931938 * 2
def baseEnd_7931938 : Nat := 4072896715662492489796687

theorem tailTrace_7931938 : CollatzResearch.WordTrace tailWord_7931938 prefixEnd_7931938 4072896715662492489796687 := by
  unfold tailWord_7931938
  simp only [CollatzResearch.WordTrace]
  refine ⟨72325386484487692001237117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192867697291967178669965645 72325386484487692001237117)
  ·
    refine ⟨27122019931682884500463919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72325386484487692001237117 27122019931682884500463919)
    ·
      refine ⟨40683029897524326750695879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27122019931682884500463919 40683029897524326750695879)
      ·
        refine ⟨61024544846286490126043819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40683029897524326750695879 61024544846286490126043819)
        ·
          refine ⟨91536817269429735189065729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61024544846286490126043819 91536817269429735189065729)
          ·
            refine ⟨68652612952072301391799297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91536817269429735189065729 68652612952072301391799297)
            ·
              refine ⟨51489459714054226043849473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68652612952072301391799297 51489459714054226043849473)
              ·
                refine ⟨38617094785540669532887105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51489459714054226043849473 38617094785540669532887105)
                ·
                  refine ⟨28962821089155502149665329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38617094785540669532887105 28962821089155502149665329)
                  ·
                    refine ⟨21722115816866626612248997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28962821089155502149665329 21722115816866626612248997)
                    ·
                      refine ⟨4072896715662492489796687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21722115816866626612248997 4072896715662492489796687)
                      ·
                        rfl

theorem cell23_7931938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_7931938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931938 prefixEnd_7931938 := by exact prefixLift 7931938
  have htrace : WordTrace (prefixWord ++ tailWord_7931938) baseStart_7931938 baseEnd_7931938 := by
    simpa [prefixWord, tailWord_7931938, baseEnd_7931938] using wordTrace_append hprefix tailTrace_7931938
  have hstable : (prefixWord ++ tailWord_7931938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931938).length < 2 ^ (prefixWord ++ tailWord_7931938).sum := by decide
  have hdescent : baseEnd_7931938 < baseStart_7931938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7931971 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 5]
def baseStart_7931971 : Nat := 118140960795 + 7931971 * 2 ^ 59
def prefixEnd_7931971 : Nat := 4983230072969 + 3 ^ 40 * 7931971 * 2
def baseEnd_7931971 : Nat := 4072913660524090860684035

theorem tailTrace_7931971 : CollatzResearch.WordTrace tailWord_7931971 prefixEnd_7931971 4072913660524090860684035 := by
  unfold tailWord_7931971
  simp only [CollatzResearch.WordTrace]
  refine ⟨289302749546831214640899767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192868499697887476427266511 289302749546831214640899767)
  ·
    refine ⟨433954124320246821961349651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289302749546831214640899767 433954124320246821961349651)
    ·
      refine ⟨650931186480370232942024477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433954124320246821961349651 650931186480370232942024477)
      ·
        refine ⟨244099194930138837353259179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 650931186480370232942024477 244099194930138837353259179)
        ·
          refine ⟨366148792395208256029888769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244099194930138837353259179 366148792395208256029888769)
          ·
            refine ⟨274611594296406192022416577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366148792395208256029888769 274611594296406192022416577)
            ·
              refine ⟨205958695722304644016812433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274611594296406192022416577 205958695722304644016812433)
              ·
                refine ⟨154469021791728483012609325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205958695722304644016812433 154469021791728483012609325)
                ·
                  refine ⟨57925883171898181129728497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154469021791728483012609325 57925883171898181129728497)
                  ·
                    refine ⟨43444412378923635847296373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57925883171898181129728497 43444412378923635847296373)
                    ·
                      refine ⟨4072913660524090860684035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43444412378923635847296373 4072913660524090860684035)
                      ·
                        rfl

theorem cell23_7931971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_7931971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7931971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7931971 prefixEnd_7931971 := by exact prefixLift 7931971
  have htrace : WordTrace (prefixWord ++ tailWord_7931971) baseStart_7931971 baseEnd_7931971 := by
    simpa [prefixWord, tailWord_7931971, baseEnd_7931971] using wordTrace_append hprefix tailTrace_7931971
  have hstable : (prefixWord ++ tailWord_7931971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7931971).length < 2 ^ (prefixWord ++ tailWord_7931971).sum := by decide
  have hdescent : baseEnd_7931971 < baseStart_7931971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7931971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932015 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 2, 4, 2]
def baseStart_7932015 : Nat := 118140960795 + 7932015 * 2 ^ 59
def prefixEnd_7932015 : Nat := 4983230072969 + 3 ^ 40 * 7932015 * 2
def baseEnd_7932015 : Nat := 4072936253672888688533833

theorem tailTrace_7932015 : CollatzResearch.WordTrace tailWord_7932015 prefixEnd_7932015 4072936253672888688533833 := by
  unfold tailWord_7932015
  simp only [CollatzResearch.WordTrace]
  refine ⟨289304354358671810155501499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192869569572447873437000999 289304354358671810155501499)
  ·
    refine ⟨433956531538007715233252249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289304354358671810155501499 433956531538007715233252249)
    ·
      refine ⟨325467398653505786424939187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433956531538007715233252249 325467398653505786424939187)
      ·
        refine ⟨488201097980258679637408781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325467398653505786424939187 488201097980258679637408781)
        ·
          refine ⟨183075411742597004864028293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 488201097980258679637408781 183075411742597004864028293)
          ·
            refine ⟨34326639701736938412005305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183075411742597004864028293 34326639701736938412005305)
            ·
              refine ⟨25744979776302703809003979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34326639701736938412005305 25744979776302703809003979)
              ·
                refine ⟨38617469664454055713505969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25744979776302703809003979 38617469664454055713505969)
                ·
                  refine ⟨28963102248340541785129477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38617469664454055713505969 28963102248340541785129477)
                  ·
                    refine ⟨5430581671563851584711777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28963102248340541785129477 5430581671563851584711777)
                    ·
                      refine ⟨4072936253672888688533833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5430581671563851584711777 4072936253672888688533833)
                      ·
                        rfl

theorem cell23_7932015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 4, 2].length) (baseStart_7932015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932015 prefixEnd_7932015 := by exact prefixLift 7932015
  have htrace : WordTrace (prefixWord ++ tailWord_7932015) baseStart_7932015 baseEnd_7932015 := by
    simpa [prefixWord, tailWord_7932015, baseEnd_7932015] using wordTrace_append hprefix tailTrace_7932015
  have hstable : (prefixWord ++ tailWord_7932015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932015).length < 2 ^ (prefixWord ++ tailWord_7932015).sum := by decide
  have hdescent : baseEnd_7932015 < baseStart_7932015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932025 : List Nat := [1, 2, 1, 3, 4, 1, 2, 2, 3, 4]
def baseStart_7932025 : Nat := 118140960795 + 7932025 * 2 ^ 59
def prefixEnd_7932025 : Nat := 4983230072969 + 3 ^ 40 * 7932025 * 2
def baseEnd_7932025 : Nat := 1357647129493144549802929

theorem tailTrace_7932025 : CollatzResearch.WordTrace tailWord_7932025 prefixEnd_7932025 1357647129493144549802929 := by
  unfold tailWord_7932025
  simp only [CollatzResearch.WordTrace]
  refine ⟨289304719088635581863365529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192869812725757054575577019 289304719088635581863365529)
  ·
    refine ⟨216978539316476686397524147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289304719088635581863365529 216978539316476686397524147)
    ·
      refine ⟨325467808974715029596286221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216978539316476686397524147 325467808974715029596286221)
      ·
        refine ⟨122050428365518136098607333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325467808974715029596286221 122050428365518136098607333)
        ·
          refine ⟨22884455318534650518488875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122050428365518136098607333 22884455318534650518488875)
          ·
            refine ⟨34326682977801975777733313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22884455318534650518488875 34326682977801975777733313)
            ·
              refine ⟨25745012233351481833299985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34326682977801975777733313 25745012233351481833299985)
              ·
                refine ⟨19308759175013611374974989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25745012233351481833299985 19308759175013611374974989)
                ·
                  refine ⟨7240784690630104265615621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19308759175013611374974989 7240784690630104265615621)
                  ·
                    refine ⟨1357647129493144549802929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7240784690630104265615621 1357647129493144549802929)
                    ·
                      rfl

theorem cell23_7932025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 4].length) (baseStart_7932025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932025 prefixEnd_7932025 := by exact prefixLift 7932025
  have htrace : WordTrace (prefixWord ++ tailWord_7932025) baseStart_7932025 baseEnd_7932025 := by
    simpa [prefixWord, tailWord_7932025, baseEnd_7932025] using wordTrace_append hprefix tailTrace_7932025
  have hstable : (prefixWord ++ tailWord_7932025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932025).length < 2 ^ (prefixWord ++ tailWord_7932025).sum := by decide
  have hdescent : baseEnd_7932025 < baseStart_7932025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932031 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 9]
def baseStart_7932031 : Nat := 118140960795 + 7932031 * 2 ^ 59
def prefixEnd_7932031 : Nat := 4983230072969 + 3 ^ 40 * 7932031 * 2
def baseEnd_7932031 : Nat := 4072944469363360625933759

theorem tailTrace_7932031 : CollatzResearch.WordTrace tailWord_7932031 prefixEnd_7932031 4072944469363360625933759 := by
  unfold tailWord_7932031
  simp only [CollatzResearch.WordTrace]
  refine ⟨289304937926613844888083947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192869958617742563258722631 289304937926613844888083947)
  ·
    refine ⟨433957406889920767332125921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289304937926613844888083947 433957406889920767332125921)
    ·
      refine ⟨325468055167440575499094441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433957406889920767332125921 325468055167440575499094441)
      ·
        refine ⟨244101041375580431624320831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325468055167440575499094441 244101041375580431624320831)
        ·
          refine ⟨366151562063370647436481247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244101041375580431624320831 366151562063370647436481247)
          ·
            refine ⟨549227343095055971154721871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366151562063370647436481247 549227343095055971154721871)
            ·
              refine ⟨823841014642583956732082807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549227343095055971154721871 823841014642583956732082807)
              ·
                refine ⟨1235761521963875935098124211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823841014642583956732082807 1235761521963875935098124211)
                ·
                  refine ⟨1853642282945813902647186317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1235761521963875935098124211 1853642282945813902647186317)
                  ·
                    refine ⟨695115856104680213492694869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1853642282945813902647186317 695115856104680213492694869)
                    ·
                      refine ⟨4072944469363360625933759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 695115856104680213492694869 4072944469363360625933759)
                      ·
                        rfl

theorem cell23_7932031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_7932031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932031 prefixEnd_7932031 := by exact prefixLift 7932031
  have htrace : WordTrace (prefixWord ++ tailWord_7932031) baseStart_7932031 baseEnd_7932031 := by
    simpa [prefixWord, tailWord_7932031, baseEnd_7932031] using wordTrace_append hprefix tailTrace_7932031
  have hstable : (prefixWord ++ tailWord_7932031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932031).length < 2 ^ (prefixWord ++ tailWord_7932031).sum := by decide
  have hdescent : baseEnd_7932031 < baseStart_7932031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932142 : List Nat := [4, 1, 2, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_7932142 : Nat := 118140960795 + 7932142 * 2 ^ 59
def prefixEnd_7932142 : Nat := 4983230072969 + 3 ^ 40 * 7932142 * 2
def baseEnd_7932142 : Nat := 4073001465716009691645749

theorem tailTrace_7932142 : CollatzResearch.WordTrace tailWord_7932142 prefixEnd_7932142 4073001465716009691645749 := by
  unfold tailWord_7932142
  simp only [CollatzResearch.WordTrace]
  refine ⟨36163623303651463855671835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192872657619474473896916453 36163623303651463855671835)
  ·
    refine ⟨54245434955477195783507753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36163623303651463855671835 54245434955477195783507753)
    ·
      refine ⟨40684076216607896837630815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54245434955477195783507753 40684076216607896837630815)
      ·
        refine ⟨61026114324911845256446223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40684076216607896837630815 61026114324911845256446223)
        ·
          refine ⟨91539171487367767884669335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61026114324911845256446223 91539171487367767884669335)
          ·
            refine ⟨137308757231051651827004003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91539171487367767884669335 137308757231051651827004003)
            ·
              refine ⟨205963135846577477740506005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137308757231051651827004003 205963135846577477740506005)
              ·
                refine ⟨9654521992808319269086219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 205963135846577477740506005 9654521992808319269086219)
                ·
                  refine ⟨14481782989212478903629329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9654521992808319269086219 14481782989212478903629329)
                  ·
                    refine ⟨10861337241909359177721997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14481782989212478903629329 10861337241909359177721997)
                    ·
                      refine ⟨4073001465716009691645749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10861337241909359177721997 4073001465716009691645749)
                      ·
                        rfl

theorem cell23_7932142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_7932142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932142 prefixEnd_7932142 := by exact prefixLift 7932142
  have htrace : WordTrace (prefixWord ++ tailWord_7932142) baseStart_7932142 baseEnd_7932142 := by
    simpa [prefixWord, tailWord_7932142, baseEnd_7932142] using wordTrace_append hprefix tailTrace_7932142
  have hstable : (prefixWord ++ tailWord_7932142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932142).length < 2 ^ (prefixWord ++ tailWord_7932142).sum := by decide
  have hdescent : baseEnd_7932142 < baseStart_7932142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932156 : List Nat := [2, 2, 2, 1, 4, 1, 1, 5, 1, 2, 2]
def baseStart_7932156 : Nat := 118140960795 + 7932156 * 2 ^ 59
def prefixEnd_7932156 : Nat := 4983230072969 + 3 ^ 40 * 7932156 * 2
def baseEnd_7932156 : Nat := 4073008654445172636870685

theorem tailTrace_7932156 : CollatzResearch.WordTrace tailWord_7932156 prefixEnd_7932156 4073008654445172636870685 := by
  unfold tailWord_7932156
  simp only [CollatzResearch.WordTrace]
  refine ⟨144654748525580495618192161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192872998034107327490922881 144654748525580495618192161)
  ·
    refine ⟨108491061394185371713644121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144654748525580495618192161 108491061394185371713644121)
    ·
      refine ⟨81368296045639028785233091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108491061394185371713644121 81368296045639028785233091)
      ·
        refine ⟨122052444068458543177849637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81368296045639028785233091 122052444068458543177849637)
        ·
          refine ⟨22884833262835976845846807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122052444068458543177849637 22884833262835976845846807)
          ·
            refine ⟨34327249894253965268770211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22884833262835976845846807 34327249894253965268770211)
            ·
              refine ⟨51490874841380947903155317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34327249894253965268770211 51490874841380947903155317)
              ·
                refine ⟨4827269516379463865920811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51490874841380947903155317 4827269516379463865920811)
                ·
                  refine ⟨7240904274569195798881217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4827269516379463865920811 7240904274569195798881217)
                  ·
                    refine ⟨5430678205926896849160913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7240904274569195798881217 5430678205926896849160913)
                    ·
                      refine ⟨4073008654445172636870685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5430678205926896849160913 4073008654445172636870685)
                      ·
                        rfl

theorem cell23_7932156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_7932156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932156 prefixEnd_7932156 := by exact prefixLift 7932156
  have htrace : WordTrace (prefixWord ++ tailWord_7932156) baseStart_7932156 baseEnd_7932156 := by
    simpa [prefixWord, tailWord_7932156, baseEnd_7932156] using wordTrace_append hprefix tailTrace_7932156
  have hstable : (prefixWord ++ tailWord_7932156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932156).length < 2 ^ (prefixWord ++ tailWord_7932156).sum := by decide
  have hdescent : baseEnd_7932156 < baseStart_7932156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932172 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 4, 1, 3]
def baseStart_7932172 : Nat := 118140960795 + 7932172 * 2 ^ 59
def prefixEnd_7932172 : Nat := 4983230072969 + 3 ^ 40 * 7932172 * 2
def baseEnd_7932172 : Nat := 4073016870135644574270611

theorem tailTrace_7932172 : CollatzResearch.WordTrace tailWord_7932172 prefixEnd_7932172 4073016870135644574270611 := by
  unfold tailWord_7932172
  simp only [CollatzResearch.WordTrace]
  refine ⟨144655040309551512984483385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192873387079402017312644513 144655040309551512984483385)
  ·
    refine ⟨108491280232163634738362539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144655040309551512984483385 108491280232163634738362539)
    ·
      refine ⟨162736920348245452107543809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108491280232163634738362539 162736920348245452107543809)
      ·
        refine ⟨122052690261184089080657857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162736920348245452107543809 122052690261184089080657857)
        ·
          refine ⟨91539517695888066810493393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122052690261184089080657857 91539517695888066810493393)
          ·
            refine ⟨68654638271916050107870045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91539517695888066810493393 68654638271916050107870045)
            ·
              refine ⟨25745489351968518790451267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68654638271916050107870045 25745489351968518790451267)
              ·
                refine ⟨38618234027952778185676901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25745489351968518790451267 38618234027952778185676901)
                ·
                  refine ⟨7240918880241145909814419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38618234027952778185676901 7240918880241145909814419)
                  ·
                    refine ⟨10861378320361718864721629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7240918880241145909814419 10861378320361718864721629)
                    ·
                      refine ⟨4073016870135644574270611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10861378320361718864721629 4073016870135644574270611)
                      ·
                        rfl

theorem cell23_7932172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_7932172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932172 prefixEnd_7932172 := by exact prefixLift 7932172
  have htrace : WordTrace (prefixWord ++ tailWord_7932172) baseStart_7932172 baseEnd_7932172 := by
    simpa [prefixWord, tailWord_7932172, baseEnd_7932172] using wordTrace_append hprefix tailTrace_7932172
  have hstable : (prefixWord ++ tailWord_7932172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932172).length < 2 ^ (prefixWord ++ tailWord_7932172).sum := by decide
  have hdescent : baseEnd_7932172 < baseStart_7932172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932289 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 2, 5, 2]
def baseStart_7932289 : Nat := 118140960795 + 7932289 * 2 ^ 59
def prefixEnd_7932289 : Nat := 4983230072969 + 3 ^ 40 * 7932289 * 2
def baseEnd_7932289 : Nat := 4073076947372220616507573

theorem tailTrace_7932289 : CollatzResearch.WordTrace tailWord_7932289 prefixEnd_7932289 4073076947372220616507573 := by
  unfold tailWord_7932289
  simp only [CollatzResearch.WordTrace]
  refine ⟨289314347959679154950975921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192876231973119436633983947 289314347959679154950975921)
  ·
    refine ⟨216985760969759366213231941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289314347959679154950975921 216985760969759366213231941)
    ·
      refine ⟨40684830181829881164980989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216985760969759366213231941 40684830181829881164980989)
      ·
        refine ⟨15256811318186205436867871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40684830181829881164980989 15256811318186205436867871)
        ·
          refine ⟨22885216977279308155301807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15256811318186205436867871 22885216977279308155301807)
          ·
            refine ⟨34327825465918962232952711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22885216977279308155301807 34327825465918962232952711)
            ·
              refine ⟨51491738198878443349429067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34327825465918962232952711 51491738198878443349429067)
              ·
                refine ⟨77237607298317665024143601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51491738198878443349429067 77237607298317665024143601)
                ·
                  refine ⟨57928205473738248768107701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77237607298317665024143601 57928205473738248768107701)
                  ·
                    refine ⟨5430769263162960822010097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57928205473738248768107701 5430769263162960822010097)
                    ·
                      refine ⟨4073076947372220616507573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5430769263162960822010097 4073076947372220616507573)
                      ·
                        rfl

theorem cell23_7932289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_7932289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932289 prefixEnd_7932289 := by exact prefixLift 7932289
  have htrace : WordTrace (prefixWord ++ tailWord_7932289) baseStart_7932289 baseEnd_7932289 := by
    simpa [prefixWord, tailWord_7932289, baseEnd_7932289] using wordTrace_append hprefix tailTrace_7932289
  have hstable : (prefixWord ++ tailWord_7932289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932289).length < 2 ^ (prefixWord ++ tailWord_7932289).sum := by decide
  have hdescent : baseEnd_7932289 < baseStart_7932289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932325 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 8]
def baseStart_7932325 : Nat := 118140960795 + 7932325 * 2 ^ 59
def prefixEnd_7932325 : Nat := 4983230072969 + 3 ^ 40 * 7932325 * 2
def baseEnd_7932325 : Nat := 452566159186198052850823

theorem tailTrace_7932325 : CollatzResearch.WordTrace tailWord_7932325 prefixEnd_7932325 452566159186198052850823 := by
  unfold tailWord_7932325
  simp only [CollatzResearch.WordTrace]
  refine ⟨289315660987548733099286429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192877107325032488732857619 289315660987548733099286429)
  ·
    refine ⟨108493372870330774912232411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289315660987548733099286429 108493372870330774912232411)
    ·
      refine ⟨162740059305496162368348617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108493372870330774912232411 162740059305496162368348617)
      ·
        refine ⟨122055044479122121776261463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162740059305496162368348617 122055044479122121776261463)
        ·
          refine ⟨183082566718683182664392195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122055044479122121776261463 183082566718683182664392195)
          ·
            refine ⟨274623850078024773996588293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183082566718683182664392195 274623850078024773996588293)
            ·
              refine ⟨51491971889629645124360305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274623850078024773996588293 51491971889629645124360305)
              ·
                refine ⟨38618978917222233843270229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51491971889629645124360305 38618978917222233843270229)
                ·
                  refine ⟨452566159186198052850823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38618978917222233843270229 452566159186198052850823)
                  ·
                    rfl

theorem cell23_7932325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 8].length) (baseStart_7932325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932325 prefixEnd_7932325 := by exact prefixLift 7932325
  have htrace : WordTrace (prefixWord ++ tailWord_7932325) baseStart_7932325 baseEnd_7932325 := by
    simpa [prefixWord, tailWord_7932325, baseEnd_7932325] using wordTrace_append hprefix tailTrace_7932325
  have hstable : (prefixWord ++ tailWord_7932325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932325).length < 2 ^ (prefixWord ++ tailWord_7932325).sum := by decide
  have hdescent : baseEnd_7932325 < baseStart_7932325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932359 : List Nat := [1, 1, 4, 1, 1, 5, 3, 1, 6]
def baseStart_7932359 : Nat := 118140960795 + 7932359 * 2 ^ 59
def prefixEnd_7932359 : Nat := 4983230072969 + 3 ^ 40 * 7932359 * 2
def baseEnd_7932359 : Nat := 452568099002003926959139

theorem tailTrace_7932359 : CollatzResearch.WordTrace tailWord_7932359 prefixEnd_7932359 452568099002003926959139 := by
  unfold tailWord_7932359
  simp only [CollatzResearch.WordTrace]
  refine ⟨289316901069425556906024131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192877934046283704604016087 289316901069425556906024131)
  ·
    refine ⟨433975351604138335359036197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289316901069425556906024131 433975351604138335359036197)
    ·
      refine ⟨81370378425775937879819287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 433975351604138335359036197 81370378425775937879819287)
      ·
        refine ⟨122055567638663906819728931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81370378425775937879819287 122055567638663906819728931)
        ·
          refine ⟨183083351457995860229593397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122055567638663906819728931 183083351457995860229593397)
          ·
            refine ⟨17164064199187111896524381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183083351457995860229593397 17164064199187111896524381)
            ·
              refine ⟨6436524074695166961196643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17164064199187111896524381 6436524074695166961196643)
              ·
                refine ⟨9654786112042750441794965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6436524074695166961196643 9654786112042750441794965)
                ·
                  refine ⟨452568099002003926959139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9654786112042750441794965 452568099002003926959139)
                  ·
                    rfl

theorem cell23_7932359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 6].length) (baseStart_7932359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932359 prefixEnd_7932359 := by exact prefixLift 7932359
  have htrace : WordTrace (prefixWord ++ tailWord_7932359) baseStart_7932359 baseEnd_7932359 := by
    simpa [prefixWord, tailWord_7932359, baseEnd_7932359] using wordTrace_append hprefix tailTrace_7932359
  have hstable : (prefixWord ++ tailWord_7932359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932359).length < 2 ^ (prefixWord ++ tailWord_7932359).sum := by decide
  have hdescent : baseEnd_7932359 < baseStart_7932359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932403 : List Nat := [1, 1, 1, 2, 2, 2, 7, 2, 1, 1, 3]
def baseStart_7932403 : Nat := 118140960795 + 7932403 * 2 ^ 59
def prefixEnd_7932403 : Nat := 4983230072969 + 3 ^ 40 * 7932403 * 2
def baseEnd_7932403 : Nat := 4073135484166833170482049

theorem tailTrace_7932403 : CollatzResearch.WordTrace tailWord_7932403 prefixEnd_7932403 4073135484166833170482049 := by
  unfold tailWord_7932403
  simp only [CollatzResearch.WordTrace]
  refine ⟨289318505881266152420625863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192879003920844101613750575 289318505881266152420625863)
  ·
    refine ⟨433977758821899228630938795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289318505881266152420625863 433977758821899228630938795)
    ·
      refine ⟨650966638232848842946408193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433977758821899228630938795 650966638232848842946408193)
      ·
        refine ⟨488224978674636632209806145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650966638232848842946408193 488224978674636632209806145)
        ·
          refine ⟨366168734005977474157354609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488224978674636632209806145 366168734005977474157354609)
          ·
            refine ⟨274626550504483105618015957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366168734005977474157354609 274626550504483105618015957)
            ·
              refine ⟨6436559777448822787922249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 274626550504483105618015957 6436559777448822787922249)
              ·
                refine ⟨4827419833086617090941687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6436559777448822787922249 4827419833086617090941687)
                ·
                  refine ⟨7241129749629925636412531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4827419833086617090941687 7241129749629925636412531)
                  ·
                    refine ⟨10861694624444888454618797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7241129749629925636412531 10861694624444888454618797)
                    ·
                      refine ⟨4073135484166833170482049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10861694624444888454618797 4073135484166833170482049)
                      ·
                        rfl

theorem cell23_7932403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 1, 1, 3].length) (baseStart_7932403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932403 prefixEnd_7932403 := by exact prefixLift 7932403
  have htrace : WordTrace (prefixWord ++ tailWord_7932403) baseStart_7932403 baseEnd_7932403 := by
    simpa [prefixWord, tailWord_7932403, baseEnd_7932403] using wordTrace_append hprefix tailTrace_7932403
  have hstable : (prefixWord ++ tailWord_7932403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932403).length < 2 ^ (prefixWord ++ tailWord_7932403).sum := by decide
  have hdescent : baseEnd_7932403 < baseStart_7932403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932412 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 2, 6, 3]
def baseStart_7932412 : Nat := 118140960795 + 7932412 * 2 ^ 59
def prefixEnd_7932412 : Nat := 4983230072969 + 3 ^ 40 * 7932412 * 2
def baseEnd_7932412 : Nat := 4073140105492723635269507

theorem tailTrace_7932412 : CollatzResearch.WordTrace tailWord_7932412 prefixEnd_7932412 4073140105492723635269507 := by
  unfold tailWord_7932412
  simp only [CollatzResearch.WordTrace]
  refine ⟨144659417069116773478851745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192879222758822364638468993 144659417069116773478851745)
  ·
    refine ⟨108494562801837580109138809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144659417069116773478851745 108494562801837580109138809)
    ·
      refine ⟨81370922101378185081854107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108494562801837580109138809 81370922101378185081854107)
      ·
        refine ⟨122056383152067277622781161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81370922101378185081854107 122056383152067277622781161)
        ·
          refine ⟨91542287364050458217085871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122056383152067277622781161 91542287364050458217085871)
          ·
            refine ⟨137313431046075687325628807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91542287364050458217085871 137313431046075687325628807)
            ·
              refine ⟨205970146569113530988443211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137313431046075687325628807 205970146569113530988443211)
              ·
                refine ⟨308955219853670296482664817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205970146569113530988443211 308955219853670296482664817)
                ·
                  refine ⟨231716414890252722361998613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308955219853670296482664817 231716414890252722361998613)
                  ·
                    refine ⟨10861706947980596360718685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 231716414890252722361998613 10861706947980596360718685)
                    ·
                      refine ⟨4073140105492723635269507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10861706947980596360718685 4073140105492723635269507)
                      ·
                        rfl

theorem cell23_7932412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_7932412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932412 prefixEnd_7932412 := by exact prefixLift 7932412
  have htrace : WordTrace (prefixWord ++ tailWord_7932412) baseStart_7932412 baseEnd_7932412 := by
    simpa [prefixWord, tailWord_7932412, baseEnd_7932412] using wordTrace_append hprefix tailTrace_7932412
  have hstable : (prefixWord ++ tailWord_7932412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932412).length < 2 ^ (prefixWord ++ tailWord_7932412).sum := by decide
  have hdescent : baseEnd_7932412 < baseStart_7932412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932419 : List Nat := [1, 1, 1, 3, 2, 1, 5, 3, 2, 4]
def baseStart_7932419 : Nat := 118140960795 + 7932419 * 2 ^ 59
def prefixEnd_7932419 : Nat := 4983230072969 + 3 ^ 40 * 7932419 * 2
def baseEnd_7932419 : Nat := 1357714566619101702627325

theorem tailTrace_7932419 : CollatzResearch.WordTrace tailWord_7932419 prefixEnd_7932419 1357714566619101702627325 := by
  unfold tailWord_7932419
  simp only [CollatzResearch.WordTrace]
  refine ⟨289319089449208187153208311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192879392966138791435472207 289319089449208187153208311)
  ·
    refine ⟨433978634173812280729812467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289319089449208187153208311 433978634173812280729812467)
    ·
      refine ⟨650967951260718421094718701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433978634173812280729812467 650967951260718421094718701)
      ·
        refine ⟨244112981722769407910519513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 650967951260718421094718701 244112981722769407910519513)
        ·
          refine ⟨183084736292077055932889635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244112981722769407910519513 183084736292077055932889635)
          ·
            refine ⟨274627104438115583899334453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183084736292077055932889635 274627104438115583899334453)
            ·
              refine ⟨25746291041073335990562605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274627104438115583899334453 25746291041073335990562605)
              ·
                refine ⟨9654859140402500996460977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25746291041073335990562605 9654859140402500996460977)
                ·
                  refine ⟨7241144355301875747345733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9654859140402500996460977 7241144355301875747345733)
                  ·
                    refine ⟨1357714566619101702627325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7241144355301875747345733 1357714566619101702627325)
                    ·
                      rfl

theorem cell23_7932419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 4].length) (baseStart_7932419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932419 prefixEnd_7932419 := by exact prefixLift 7932419
  have htrace : WordTrace (prefixWord ++ tailWord_7932419) baseStart_7932419 baseEnd_7932419 := by
    simpa [prefixWord, tailWord_7932419, baseEnd_7932419] using wordTrace_append hprefix tailTrace_7932419
  have hstable : (prefixWord ++ tailWord_7932419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932419).length < 2 ^ (prefixWord ++ tailWord_7932419).sum := by decide
  have hdescent : baseEnd_7932419 < baseStart_7932419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932423 : List Nat := [1, 1, 4, 3, 4, 1, 1, 2, 1, 5]
def baseStart_7932423 : Nat := 118140960795 + 7932423 * 2 ^ 59
def prefixEnd_7932423 : Nat := 4983230072969 + 3 ^ 40 * 7932423 * 2
def baseEnd_7932423 : Nat := 1357715251259974364077319

theorem tailTrace_7932423 : CollatzResearch.WordTrace tailWord_7932423 prefixEnd_7932423 1357715251259974364077319 := by
  unfold tailWord_7932423
  simp only [CollatzResearch.WordTrace]
  refine ⟨289319235341193695836353923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192879490227462463890902615 289319235341193695836353923)
  ·
    refine ⟨433978853011790543754530885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289319235341193695836353923 433978853011790543754530885)
    ·
      refine ⟨81371034939710726953974541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 433978853011790543754530885 81371034939710726953974541)
      ·
        refine ⟨30514138102391522607740453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81371034939710726953974541 30514138102391522607740453)
        ·
          refine ⟨5721400894198410488951335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30514138102391522607740453 5721400894198410488951335)
          ·
            refine ⟨8582101341297615733427003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5721400894198410488951335 8582101341297615733427003)
            ·
              refine ⟨12873152011946423600140505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8582101341297615733427003 12873152011946423600140505)
              ·
                refine ⟨9654864008959817700105379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12873152011946423600140505 9654864008959817700105379)
                ·
                  refine ⟨14482296013439726550158069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9654864008959817700105379 14482296013439726550158069)
                  ·
                    refine ⟨1357715251259974364077319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14482296013439726550158069 1357715251259974364077319)
                    ·
                      rfl

theorem cell23_7932423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_7932423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932423 prefixEnd_7932423 := by exact prefixLift 7932423
  have htrace : WordTrace (prefixWord ++ tailWord_7932423) baseStart_7932423 baseEnd_7932423 := by
    simpa [prefixWord, tailWord_7932423, baseEnd_7932423] using wordTrace_append hprefix tailTrace_7932423
  have hstable : (prefixWord ++ tailWord_7932423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932423).length < 2 ^ (prefixWord ++ tailWord_7932423).sum := by decide
  have hdescent : baseEnd_7932423 < baseStart_7932423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932426 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 5, 2, 2]
def baseStart_7932426 : Nat := 118140960795 + 7932426 * 2 ^ 59
def prefixEnd_7932426 : Nat := 4983230072969 + 3 ^ 40 * 7932426 * 2
def baseEnd_7932426 : Nat := 4073147294221886580494443

theorem tailTrace_7932426 : CollatzResearch.WordTrace tailWord_7932426 prefixEnd_7932426 4073147294221886580494443 := by
  unfold tailWord_7932426
  simp only [CollatzResearch.WordTrace]
  refine ⟨72329836190045706837178283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192879563173455218232475421 72329836190045706837178283)
  ·
    refine ⟨108494754285068560255767425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72329836190045706837178283 108494754285068560255767425)
    ·
      refine ⟨81371065713801420191825569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108494754285068560255767425 81371065713801420191825569)
      ·
        refine ⟨61028299285351065143869177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81371065713801420191825569 61028299285351065143869177)
        ·
          refine ⟨45771224464013298857901883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61028299285351065143869177 45771224464013298857901883)
          ·
            refine ⟨68656836696019948286852825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45771224464013298857901883 68656836696019948286852825)
            ·
              refine ⟨51492627522014961215139619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68656836696019948286852825 51492627522014961215139619)
              ·
                refine ⟨77238941283022441822709429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51492627522014961215139619 77238941283022441822709429)
                ·
                  refine ⟨7241150745283353920879009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77238941283022441822709429 7241150745283353920879009)
                  ·
                    refine ⟨5430863058962515440659257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7241150745283353920879009 5430863058962515440659257)
                    ·
                      refine ⟨4073147294221886580494443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5430863058962515440659257 4073147294221886580494443)
                      ·
                        rfl

theorem cell23_7932426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_7932426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932426 prefixEnd_7932426 := by exact prefixLift 7932426
  have htrace : WordTrace (prefixWord ++ tailWord_7932426) baseStart_7932426 baseEnd_7932426 := by
    simpa [prefixWord, tailWord_7932426, baseEnd_7932426] using wordTrace_append hprefix tailTrace_7932426
  have hstable : (prefixWord ++ tailWord_7932426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932426).length < 2 ^ (prefixWord ++ tailWord_7932426).sum := by decide
  have hdescent : baseEnd_7932426 < baseStart_7932426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932436 : List Nat := [2, 4, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_7932436 : Nat := 118140960795 + 7932436 * 2 ^ 59
def prefixEnd_7932436 : Nat := 4983230072969 + 3 ^ 40 * 7932436 * 2
def baseEnd_7932436 : Nat := 1357717476342810513789799

theorem tailTrace_7932436 : CollatzResearch.WordTrace tailWord_7932436 prefixEnd_7932436 1357717476342810513789799 := by
  unfold tailWord_7932436
  simp only [CollatzResearch.WordTrace]
  refine ⟨144659854745073299528288581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192879806326764399371051441 144659854745073299528288581)
  ·
    refine ⟨27123722764701243661554109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144659854745073299528288581 27123722764701243661554109)
    ·
      refine ⟨10171396036762966373082791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27123722764701243661554109 10171396036762966373082791)
      ·
        refine ⟨15257094055144449559624187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10171396036762966373082791 15257094055144449559624187)
        ·
          refine ⟨22885641082716674339436281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15257094055144449559624187 22885641082716674339436281)
          ·
            refine ⟨17164230812037505754577211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22885641082716674339436281 17164230812037505754577211)
            ·
              refine ⟨25746346218056258631865817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17164230812037505754577211 25746346218056258631865817)
              ·
                refine ⟨19309759663542193973899363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25746346218056258631865817 19309759663542193973899363)
                ·
                  refine ⟨28964639495313290960849045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19309759663542193973899363 28964639495313290960849045)
                  ·
                    refine ⟨1357717476342810513789799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28964639495313290960849045 1357717476342810513789799)
                    ·
                      rfl

theorem cell23_7932436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_7932436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932436 prefixEnd_7932436 := by exact prefixLift 7932436
  have htrace : WordTrace (prefixWord ++ tailWord_7932436) baseStart_7932436 baseEnd_7932436 := by
    simpa [prefixWord, tailWord_7932436, baseEnd_7932436] using wordTrace_append hprefix tailTrace_7932436
  have hstable : (prefixWord ++ tailWord_7932436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932436).length < 2 ^ (prefixWord ++ tailWord_7932436).sum := by decide
  have hdescent : baseEnd_7932436 < baseStart_7932436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932459 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 4, 1, 3]
def baseStart_7932459 : Nat := 118140960795 + 7932459 * 2 ^ 59
def prefixEnd_7932459 : Nat := 4983230072969 + 3 ^ 40 * 7932459 * 2
def baseEnd_7932459 : Nat := 4073164239083484951381791

theorem tailTrace_7932459 : CollatzResearch.WordTrace tailWord_7932459 prefixEnd_7932459 4073164239083484951381791 := by
  unfold tailWord_7932459
  simp only [CollatzResearch.WordTrace]
  refine ⟨289320548369063273984664431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192880365579375515989776287 289320548369063273984664431)
  ·
    refine ⟨433980822553594910976996647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289320548369063273984664431 433980822553594910976996647)
    ·
      refine ⟨650971233830392366465494971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433980822553594910976996647 650971233830392366465494971)
      ·
        refine ⟨976456850745588549698242457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650971233830392366465494971 976456850745588549698242457)
        ·
          refine ⟨732342638059191412273681843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 976456850745588549698242457 732342638059191412273681843)
          ·
            refine ⟨1098513957088787118410522765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732342638059191412273681843 1098513957088787118410522765)
            ·
              refine ⟨411942733908295169403946037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1098513957088787118410522765 411942733908295169403946037)
              ·
                refine ⟨38619631303902672131619941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 411942733908295169403946037 38619631303902672131619941)
                ·
                  refine ⟨7241180869481751024678739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38619631303902672131619941 7241180869481751024678739)
                  ·
                    refine ⟨10861771304222626537018109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7241180869481751024678739 10861771304222626537018109)
                    ·
                      refine ⟨4073164239083484951381791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10861771304222626537018109 4073164239083484951381791)
                      ·
                        rfl

theorem cell23_7932459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 1, 3].length) (baseStart_7932459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932459 prefixEnd_7932459 := by exact prefixLift 7932459
  have htrace : WordTrace (prefixWord ++ tailWord_7932459) baseStart_7932459 baseEnd_7932459 := by
    simpa [prefixWord, tailWord_7932459, baseEnd_7932459] using wordTrace_append hprefix tailTrace_7932459
  have hstable : (prefixWord ++ tailWord_7932459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932459).length < 2 ^ (prefixWord ++ tailWord_7932459).sum := by decide
  have hdescent : baseEnd_7932459 < baseStart_7932459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932476 : List Nat := [2, 2, 2, 2, 3, 2, 2, 1, 1, 3, 3]
def baseStart_7932476 : Nat := 118140960795 + 7932476 * 2 ^ 59
def prefixEnd_7932476 : Nat := 4983230072969 + 3 ^ 40 * 7932476 * 2
def baseEnd_7932476 : Nat := 4073172968254611384869213

theorem tailTrace_7932476 : CollatzResearch.WordTrace tailWord_7932476 prefixEnd_7932476 4073172968254611384869213 := by
  unfold tailWord_7932476
  simp only [CollatzResearch.WordTrace]
  refine ⟨144660584205000842944016641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192880778940001123925355521 144660584205000842944016641)
  ·
    refine ⟨108495438153750632208012481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144660584205000842944016641 108495438153750632208012481)
    ·
      refine ⟨81371578615312974156009361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108495438153750632208012481 81371578615312974156009361)
      ·
        refine ⟨61028683961484730617007021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81371578615312974156009361 61028683961484730617007021)
        ·
          refine ⟨22885756485556773981377633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61028683961484730617007021 22885756485556773981377633)
          ·
            refine ⟨17164317364167580486033225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22885756485556773981377633 17164317364167580486033225)
            ·
              refine ⟨12873238023125685364524919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17164317364167580486033225 12873238023125685364524919)
              ·
                refine ⟨19309857034688528046787379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12873238023125685364524919 19309857034688528046787379)
                ·
                  refine ⟨28964785552032792070181069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19309857034688528046787379 28964785552032792070181069)
                  ·
                    refine ⟨10861794582012297026317901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28964785552032792070181069 10861794582012297026317901)
                    ·
                      refine ⟨4073172968254611384869213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10861794582012297026317901 4073172968254611384869213)
                      ·
                        rfl

theorem cell23_7932476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_7932476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932476 prefixEnd_7932476 := by exact prefixLift 7932476
  have htrace : WordTrace (prefixWord ++ tailWord_7932476) baseStart_7932476 baseEnd_7932476 := by
    simpa [prefixWord, tailWord_7932476, baseEnd_7932476] using wordTrace_append hprefix tailTrace_7932476
  have hstable : (prefixWord ++ tailWord_7932476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932476).length < 2 ^ (prefixWord ++ tailWord_7932476).sum := by decide
  have hdescent : baseEnd_7932476 < baseStart_7932476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932492 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 1, 8]
def baseStart_7932492 : Nat := 118140960795 + 7932492 * 2 ^ 59
def prefixEnd_7932492 : Nat := 4983230072969 + 3 ^ 40 * 7932492 * 2
def baseEnd_7932492 : Nat := 1357727061315027774089713

theorem tailTrace_7932492 : CollatzResearch.WordTrace tailWord_7932492 prefixEnd_7932492 1357727061315027774089713 := by
  unfold tailWord_7932492
  simp only [CollatzResearch.WordTrace]
  refine ⟨144660875988971860310307865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192881167985295813747077153 144660875988971860310307865)
  ·
    refine ⟨108495656991728895232730899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144660875988971860310307865 108495656991728895232730899)
    ·
      refine ⟨162743485487593342849096349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108495656991728895232730899 162743485487593342849096349)
      ·
        refine ⟨61028807057847503568411131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162743485487593342849096349 61028807057847503568411131)
        ·
          refine ⟨91543210586771255352616697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61028807057847503568411131 91543210586771255352616697)
          ·
            refine ⟨68657407940078441514462523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91543210586771255352616697 68657407940078441514462523)
            ·
              refine ⟨102986111910117662271693785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68657407940078441514462523 102986111910117662271693785)
              ·
                refine ⟨77239583932588246703770339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102986111910117662271693785 77239583932588246703770339)
                ·
                  refine ⟨115859375898882370055655509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77239583932588246703770339 115859375898882370055655509)
                  ·
                    refine ⟨1357727061315027774089713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115859375898882370055655509 1357727061315027774089713)
                    ·
                      rfl

theorem cell23_7932492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_7932492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932492 prefixEnd_7932492 := by exact prefixLift 7932492
  have htrace : WordTrace (prefixWord ++ tailWord_7932492) baseStart_7932492 baseEnd_7932492 := by
    simpa [prefixWord, tailWord_7932492, baseEnd_7932492] using wordTrace_append hprefix tailTrace_7932492
  have hstable : (prefixWord ++ tailWord_7932492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932492).length < 2 ^ (prefixWord ++ tailWord_7932492).sum := by decide
  have hdescent : baseEnd_7932492 < baseStart_7932492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932569 : List Nat := [1, 2, 1, 2, 1, 2, 5, 2, 2, 5]
def baseStart_7932569 : Nat := 118140960795 + 7932569 * 2 ^ 59
def prefixEnd_7932569 : Nat := 4983230072969 + 3 ^ 40 * 7932569 * 2
def baseEnd_7932569 : Nat := 1357740240651826507002095

theorem tailTrace_7932569 : CollatzResearch.WordTrace tailWord_7932569 prefixEnd_7932569 1357740240651826507002095 := by
  unfold tailWord_7932569
  simp only [CollatzResearch.WordTrace]
  refine ⟨289324560398664762771168761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192883040265776508514112507 289324560398664762771168761)
  ·
    refine ⟨216993420298998572078376571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289324560398664762771168761 216993420298998572078376571)
    ·
      refine ⟨325490130448497858117564857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216993420298998572078376571 325490130448497858117564857)
      ·
        refine ⟨244117597836373393588173643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325490130448497858117564857 244117597836373393588173643)
        ·
          refine ⟨366176396754560090382260465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244117597836373393588173643 366176396754560090382260465)
          ·
            refine ⟨274632297565920067786695349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366176396754560090382260465 274632297565920067786695349)
            ·
              refine ⟨25746777896805006355002689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274632297565920067786695349 25746777896805006355002689)
              ·
                refine ⟨19310083422603754766252017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25746777896805006355002689 19310083422603754766252017)
                ·
                  refine ⟨14482562566952816074689013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19310083422603754766252017 14482562566952816074689013)
                  ·
                    refine ⟨1357740240651826507002095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14482562566952816074689013 1357740240651826507002095)
                    ·
                      rfl

theorem cell23_7932569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 5].length) (baseStart_7932569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932569 prefixEnd_7932569 := by exact prefixLift 7932569
  have htrace : WordTrace (prefixWord ++ tailWord_7932569) baseStart_7932569 baseEnd_7932569 := by
    simpa [prefixWord, tailWord_7932569, baseEnd_7932569] using wordTrace_append hprefix tailTrace_7932569
  have hstable : (prefixWord ++ tailWord_7932569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932569).length < 2 ^ (prefixWord ++ tailWord_7932569).sum := by decide
  have hdescent : baseEnd_7932569 < baseStart_7932569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932633 : List Nat := [1, 2, 1, 2, 3, 2, 3, 4, 1, 4]
def baseStart_7932633 : Nat := 118140960795 + 7932633 * 2 ^ 59
def prefixEnd_7932633 : Nat := 4983230072969 + 3 ^ 40 * 7932633 * 2
def baseEnd_7932633 : Nat := 1357751194905789090201997

theorem tailTrace_7932633 : CollatzResearch.WordTrace tailWord_7932633 prefixEnd_7932633 1357751194905789090201997 := by
  unfold tailWord_7932633
  simp only [CollatzResearch.WordTrace]
  refine ⟨289326894670432901701498553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192884596446955267800999035 289326894670432901701498553)
  ·
    refine ⟨216995171002824676276123915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289326894670432901701498553 216995171002824676276123915)
    ·
      refine ⟨325492756504237014414185873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216995171002824676276123915 325492756504237014414185873)
      ·
        refine ⟨244119567378177760810639405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325492756504237014414185873 244119567378177760810639405)
        ·
          refine ⟨91544837766816660303989777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244119567378177760810639405 91544837766816660303989777)
          ·
            refine ⟨68658628325112495227992333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91544837766816660303989777 68658628325112495227992333)
            ·
              refine ⟨25746985621917185710497125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68658628325112495227992333 25746985621917185710497125)
              ·
                refine ⟨4827559804109472320718211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25746985621917185710497125 4827559804109472320718211)
                ·
                  refine ⟨7241339706164208481077317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4827559804109472320718211 7241339706164208481077317)
                  ·
                    refine ⟨1357751194905789090201997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7241339706164208481077317 1357751194905789090201997)
                    ·
                      rfl

theorem cell23_7932633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 1, 4].length) (baseStart_7932633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932633 prefixEnd_7932633 := by exact prefixLift 7932633
  have htrace : WordTrace (prefixWord ++ tailWord_7932633) baseStart_7932633 baseEnd_7932633 := by
    simpa [prefixWord, tailWord_7932633, baseEnd_7932633] using wordTrace_append hprefix tailTrace_7932633
  have hstable : (prefixWord ++ tailWord_7932633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932633).length < 2 ^ (prefixWord ++ tailWord_7932633).sum := by decide
  have hdescent : baseEnd_7932633 < baseStart_7932633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932689 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 3, 6]
def baseStart_7932689 : Nat := 118140960795 + 7932689 * 2 ^ 59
def prefixEnd_7932689 : Nat := 4983230072969 + 3 ^ 40 * 7932689 * 2
def baseEnd_7932689 : Nat := 1357760779878006350501911

theorem tailTrace_7932689 : CollatzResearch.WordTrace tailWord_7932689 prefixEnd_7932689 1357760779878006350501911 := by
  unfold tailWord_7932689
  simp only [CollatzResearch.WordTrace]
  refine ⟨289328937158230023265537121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192885958105486682177024747 289328937158230023265537121)
  ·
    refine ⟨216996702868672517449152841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289328937158230023265537121 216996702868672517449152841)
    ·
      refine ⟨162747527151504388086864631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216996702868672517449152841 162747527151504388086864631)
      ·
        refine ⟨244121290727256582130296947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162747527151504388086864631 244121290727256582130296947)
        ·
          refine ⟨366181936090884873195445421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244121290727256582130296947 366181936090884873195445421)
          ·
            refine ⟨137318226034081827448292033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366181936090884873195445421 137318226034081827448292033)
            ·
              refine ⟨102988669525561370586219025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137318226034081827448292033 102988669525561370586219025)
              ·
                refine ⟨77241502144171027939664269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102988669525561370586219025 77241502144171027939664269)
                ·
                  refine ⟨28965563304064135477374101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77241502144171027939664269 28965563304064135477374101)
                  ·
                    refine ⟨1357760779878006350501911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28965563304064135477374101 1357760779878006350501911)
                    ·
                      rfl

theorem cell23_7932689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_7932689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932689 prefixEnd_7932689 := by exact prefixLift 7932689
  have htrace : WordTrace (prefixWord ++ tailWord_7932689) baseStart_7932689 baseEnd_7932689 := by
    simpa [prefixWord, tailWord_7932689, baseEnd_7932689] using wordTrace_append hprefix tailTrace_7932689
  have hstable : (prefixWord ++ tailWord_7932689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932689).length < 2 ^ (prefixWord ++ tailWord_7932689).sum := by decide
  have hdescent : baseEnd_7932689 < baseStart_7932689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932746 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 5, 3, 3]
def baseStart_7932746 : Nat := 118140960795 + 7932746 * 2 ^ 59
def prefixEnd_7932746 : Nat := 4983230072969 + 3 ^ 40 * 7932746 * 2
def baseEnd_7932746 : Nat := 4073311608031325328492971

theorem tailTrace_7932746 : CollatzResearch.WordTrace tailWord_7932746 prefixEnd_7932746 4073311608031325328492971 := by
  unfold tailWord_7932746
  simp only [CollatzResearch.WordTrace]
  refine ⟨72332754029755880500090523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192887344079349014666908061 72332754029755880500090523)
  ·
    refine ⟨108499131044633820750135785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72332754029755880500090523 108499131044633820750135785)
    ·
      refine ⟨81374348283475365562601839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108499131044633820750135785 81374348283475365562601839)
      ·
        refine ⟨122061522425213048343902759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81374348283475365562601839 122061522425213048343902759)
        ·
          refine ⟨183092283637819572515854139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122061522425213048343902759 183092283637819572515854139)
          ·
            refine ⟨274638425456729358773781209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183092283637819572515854139 274638425456729358773781209)
            ·
              refine ⟨205978819092547019080335907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274638425456729358773781209 205978819092547019080335907)
              ·
                refine ⟨308968228638820528620503861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205978819092547019080335907 308968228638820528620503861)
                ·
                  refine ⟨28965771434889424558172237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 308968228638820528620503861 28965771434889424558172237)
                  ·
                    refine ⟨10862164288083534209314589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28965771434889424558172237 10862164288083534209314589)
                    ·
                      refine ⟨4073311608031325328492971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10862164288083534209314589 4073311608031325328492971)
                      ·
                        rfl

theorem cell23_7932746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_7932746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932746 prefixEnd_7932746 := by exact prefixLift 7932746
  have htrace : WordTrace (prefixWord ++ tailWord_7932746) baseStart_7932746 baseEnd_7932746 := by
    simpa [prefixWord, tailWord_7932746, baseEnd_7932746] using wordTrace_append hprefix tailTrace_7932746
  have hstable : (prefixWord ++ tailWord_7932746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932746).length < 2 ^ (prefixWord ++ tailWord_7932746).sum := by decide
  have hdescent : baseEnd_7932746 < baseStart_7932746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932803 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 3, 4, 2]
def baseStart_7932803 : Nat := 118140960795 + 7932803 * 2 ^ 59
def prefixEnd_7932803 : Nat := 4983230072969 + 3 ^ 40 * 7932803 * 2
def baseEnd_7932803 : Nat := 4073340876428631605480209

theorem tailTrace_7932803 : CollatzResearch.WordTrace tailWord_7932803 prefixEnd_7932803 4073340876428631605480209 := by
  unfold tailWord_7932803
  simp only [CollatzResearch.WordTrace]
  refine ⟨289333095079817020735187063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192888730053211347156791375 289333095079817020735187063)
  ·
    refine ⟨433999642619725531102780595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289333095079817020735187063 433999642619725531102780595)
    ·
      refine ⟨650999463929588296654170893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433999642619725531102780595 650999463929588296654170893)
      ·
        refine ⟨244124798973595611245314085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 650999463929588296654170893 244124798973595611245314085)
        ·
          refine ⟨45773399807549177108496391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244124798973595611245314085 45773399807549177108496391)
          ·
            refine ⟨68660099711323765662744587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45773399807549177108496391 68660099711323765662744587)
            ·
              refine ⟨102990149566985648494116881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68660099711323765662744587 102990149566985648494116881)
              ·
                refine ⟨77242612175239236370587661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102990149566985648494116881 77242612175239236370587661)
                ·
                  refine ⟨28965979565714713638970373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77242612175239236370587661 28965979565714713638970373)
                  ·
                    refine ⟨5431121168571508807306945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28965979565714713638970373 5431121168571508807306945)
                    ·
                      refine ⟨4073340876428631605480209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5431121168571508807306945 4073340876428631605480209)
                      ·
                        rfl

theorem cell23_7932803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 4, 2].length) (baseStart_7932803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932803 prefixEnd_7932803 := by exact prefixLift 7932803
  have htrace : WordTrace (prefixWord ++ tailWord_7932803) baseStart_7932803 baseEnd_7932803 := by
    simpa [prefixWord, tailWord_7932803, baseEnd_7932803] using wordTrace_append hprefix tailTrace_7932803
  have hstable : (prefixWord ++ tailWord_7932803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932803).length < 2 ^ (prefixWord ++ tailWord_7932803).sum := by decide
  have hdescent : baseEnd_7932803 < baseStart_7932803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932853 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_7932853 : Nat := 118140960795 + 7932853 * 2 ^ 59
def prefixEnd_7932853 : Nat := 4983230072969 + 3 ^ 40 * 7932853 * 2
def baseEnd_7932853 : Nat := 4073366550461356409854979

theorem tailTrace_7932853 : CollatzResearch.WordTrace tailWord_7932853 prefixEnd_7932853 4073366550461356409854979 := by
  unfold tailWord_7932853
  simp only [CollatzResearch.WordTrace]
  refine ⟨289334918729635879274507213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192889945819757252849671475 289334918729635879274507213)
  ·
    refine ⟨108500594523613454727940205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289334918729635879274507213 108500594523613454727940205)
    ·
      refine ⟨40687722946355045522977577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108500594523613454727940205 40687722946355045522977577)
      ·
        refine ⟨30515792209766284142233183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40687722946355045522977577 30515792209766284142233183)
        ·
          refine ⟨45773688314649426213349775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30515792209766284142233183 45773688314649426213349775)
          ·
            refine ⟨68660532471974139320024663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45773688314649426213349775 68660532471974139320024663)
            ·
              refine ⟨102990798707961208980036995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68660532471974139320024663 102990798707961208980036995)
              ·
                refine ⟨154486198061941813470055493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102990798707961208980036995 154486198061941813470055493)
                ·
                  refine ⟨28966162136614090025635405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154486198061941813470055493 28966162136614090025635405)
                  ·
                    refine ⟨10862310801230283759613277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28966162136614090025635405 10862310801230283759613277)
                    ·
                      refine ⟨4073366550461356409854979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10862310801230283759613277 4073366550461356409854979)
                      ·
                        rfl

theorem cell23_7932853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_7932853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932853 prefixEnd_7932853 := by exact prefixLift 7932853
  have htrace : WordTrace (prefixWord ++ tailWord_7932853) baseStart_7932853 baseEnd_7932853 := by
    simpa [prefixWord, tailWord_7932853, baseEnd_7932853] using wordTrace_append hprefix tailTrace_7932853
  have hstable : (prefixWord ++ tailWord_7932853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932853).length < 2 ^ (prefixWord ++ tailWord_7932853).sum := by decide
  have hdescent : baseEnd_7932853 < baseStart_7932853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932863 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 2, 5, 2]
def baseStart_7932863 : Nat := 118140960795 + 7932863 * 2 ^ 59
def prefixEnd_7932863 : Nat := 4983230072969 + 3 ^ 40 * 7932863 * 2
def baseEnd_7932863 : Nat := 4073371685267901370729933

theorem tailTrace_7932863 : CollatzResearch.WordTrace tailWord_7932863 prefixEnd_7932863 4073371685267901370729933 := by
  unfold tailWord_7932863
  simp only [CollatzResearch.WordTrace]
  refine ⟨289335283459599650982371243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192890188973066433988247495 289335283459599650982371243)
  ·
    refine ⟨434002925189399476473556865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289335283459599650982371243 434002925189399476473556865)
    ·
      refine ⟨325502193892049607355167649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434002925189399476473556865 325502193892049607355167649)
      ·
        refine ⟨244126645419037205516375737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325502193892049607355167649 244126645419037205516375737)
        ·
          refine ⟨183094984064277904137281803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244126645419037205516375737 183094984064277904137281803)
          ·
            refine ⟨274642476096416856205922705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183094984064277904137281803 274642476096416856205922705)
            ·
              refine ⟨205981857072312642154442029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274642476096416856205922705 205981857072312642154442029)
              ·
                refine ⟨77243196402117240807915761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205981857072312642154442029 77243196402117240807915761)
                ·
                  refine ⟨57932397301587930605936821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77243196402117240807915761 57932397301587930605936821)
                  ·
                    refine ⟨5431162247023868494306577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57932397301587930605936821 5431162247023868494306577)
                    ·
                      refine ⟨4073371685267901370729933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5431162247023868494306577 4073371685267901370729933)
                      ·
                        rfl

theorem cell23_7932863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 5, 2].length) (baseStart_7932863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932863 prefixEnd_7932863 := by exact prefixLift 7932863
  have htrace : WordTrace (prefixWord ++ tailWord_7932863) baseStart_7932863 baseEnd_7932863 := by
    simpa [prefixWord, tailWord_7932863, baseEnd_7932863] using wordTrace_append hprefix tailTrace_7932863
  have hstable : (prefixWord ++ tailWord_7932863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932863).length < 2 ^ (prefixWord ++ tailWord_7932863).sum := by decide
  have hdescent : baseEnd_7932863 < baseStart_7932863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932896 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 5]
def baseStart_7932896 : Nat := 118140960795 + 7932896 * 2 ^ 59
def prefixEnd_7932896 : Nat := 4983230072969 + 3 ^ 40 * 7932896 * 2
def baseEnd_7932896 : Nat := 4073388630129499741617281

theorem tailTrace_7932896 : CollatzResearch.WordTrace tailWord_7932896 prefixEnd_7932896 4073388630129499741617281 := by
  unfold tailWord_7932896
  simp only [CollatzResearch.WordTrace]
  refine ⟨144668243534240048809161271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192890991378986731745548361 144668243534240048809161271)
  ·
    refine ⟨217002365301360073213741907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144668243534240048809161271 217002365301360073213741907)
    ·
      refine ⟨325503547952040109820612861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217002365301360073213741907 325503547952040109820612861)
      ·
        refine ⟨122063830482015041182729823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325503547952040109820612861 122063830482015041182729823)
        ·
          refine ⟨183095745723022561774094735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122063830482015041182729823 183095745723022561774094735)
          ·
            refine ⟨274643618584533842661142103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183095745723022561774094735 274643618584533842661142103)
            ·
              refine ⟨411965427876800763991713155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274643618584533842661142103 411965427876800763991713155)
              ·
                refine ⟨617948141815201145987569733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411965427876800763991713155 617948141815201145987569733)
                ·
                  refine ⟨115865276590350214872669325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 617948141815201145987569733 115865276590350214872669325)
                  ·
                    refine ⟨43449478721381330577250997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115865276590350214872669325 43449478721381330577250997)
                    ·
                      refine ⟨4073388630129499741617281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43449478721381330577250997 4073388630129499741617281)
                      ·
                        rfl

theorem cell23_7932896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_7932896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932896 prefixEnd_7932896 := by exact prefixLift 7932896
  have htrace : WordTrace (prefixWord ++ tailWord_7932896) baseStart_7932896 baseEnd_7932896 := by
    simpa [prefixWord, tailWord_7932896, baseEnd_7932896] using wordTrace_append hprefix tailTrace_7932896
  have hstable : (prefixWord ++ tailWord_7932896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932896).length < 2 ^ (prefixWord ++ tailWord_7932896).sum := by decide
  have hdescent : baseEnd_7932896 < baseStart_7932896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932917 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_7932917 : Nat := 118140960795 + 7932917 * 2 ^ 59
def prefixEnd_7932917 : Nat := 4983230072969 + 3 ^ 40 * 7932917 * 2
def baseEnd_7932917 : Nat := 4073399413223244159454685

theorem tailTrace_7932917 : CollatzResearch.WordTrace tailWord_7932917 prefixEnd_7932917 4073399413223244159454685 := by
  unfold tailWord_7932917
  simp only [CollatzResearch.WordTrace]
  refine ⟨289337253001404018204837005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192891502000936012136558003 289337253001404018204837005)
  ·
    refine ⟨108501469875526506826813877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289337253001404018204837005 108501469875526506826813877)
    ·
      refine ⟨10172012800830610015013801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108501469875526506826813877 10172012800830610015013801)
      ·
        refine ⟨7629009600622957511260351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10172012800830610015013801 7629009600622957511260351)
        ·
          refine ⟨11443514400934436266890527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7629009600622957511260351 11443514400934436266890527)
          ·
            refine ⟨17165271601401654400335791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11443514400934436266890527 17165271601401654400335791)
            ·
              refine ⟨25747907402102481600503687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17165271601401654400335791 25747907402102481600503687)
              ·
                refine ⟨38621861103153722400755531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25747907402102481600503687 38621861103153722400755531)
                ·
                  refine ⟨57932791654730583601133297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38621861103153722400755531 57932791654730583601133297)
                  ·
                    refine ⟨43449593741047937700849973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57932791654730583601133297 43449593741047937700849973)
                    ·
                      refine ⟨4073399413223244159454685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43449593741047937700849973 4073399413223244159454685)
                      ·
                        rfl

theorem cell23_7932917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_7932917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932917 prefixEnd_7932917 := by exact prefixLift 7932917
  have htrace : WordTrace (prefixWord ++ tailWord_7932917) baseStart_7932917 baseEnd_7932917 := by
    simpa [prefixWord, tailWord_7932917, baseEnd_7932917] using wordTrace_append hprefix tailTrace_7932917
  have hstable : (prefixWord ++ tailWord_7932917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932917).length < 2 ^ (prefixWord ++ tailWord_7932917).sum := by decide
  have hdescent : baseEnd_7932917 < baseStart_7932917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932933 : List Nat := [1, 3, 1, 1, 2, 3, 3, 3, 6]
def baseStart_7932933 : Nat := 118140960795 + 7932933 * 2 ^ 59
def prefixEnd_7932933 : Nat := 4983230072969 + 3 ^ 40 * 7932933 * 2
def baseEnd_7932933 : Nat := 452600847657079566317179

theorem tailTrace_7932933 : CollatzResearch.WordTrace tailWord_7932933 prefixEnd_7932933 452600847657079566317179 := by
  unfold tailWord_7932933
  simp only [CollatzResearch.WordTrace]
  refine ⟨289337836569346052937419453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192891891046230701958279635 289337836569346052937419453)
  ·
    refine ⟨108501688713504769851532295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289337836569346052937419453 108501688713504769851532295)
    ·
      refine ⟨162752533070257154777298443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108501688713504769851532295 162752533070257154777298443)
      ·
        refine ⟨244128799605385732165947665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162752533070257154777298443 244128799605385732165947665)
        ·
          refine ⟨183096599704039299124460749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244128799605385732165947665 183096599704039299124460749)
          ·
            refine ⟨68661224889014737171672781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183096599704039299124460749 68661224889014737171672781)
            ·
              refine ⟨25747959333380526439377293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68661224889014737171672781 25747959333380526439377293)
              ·
                refine ⟨9655484750017697414766485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25747959333380526439377293 9655484750017697414766485)
                ·
                  refine ⟨452600847657079566317179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9655484750017697414766485 452600847657079566317179)
                  ·
                    rfl

theorem cell23_7932933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 6].length) (baseStart_7932933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932933 prefixEnd_7932933 := by exact prefixLift 7932933
  have htrace : WordTrace (prefixWord ++ tailWord_7932933) baseStart_7932933 baseEnd_7932933 := by
    simpa [prefixWord, tailWord_7932933, baseEnd_7932933] using wordTrace_append hprefix tailTrace_7932933
  have hstable : (prefixWord ++ tailWord_7932933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932933).length < 2 ^ (prefixWord ++ tailWord_7932933).sum := by decide
  have hdescent : baseEnd_7932933 < baseStart_7932933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7932967 : List Nat := [1, 1, 7, 1, 1, 2, 2, 2, 6]
def baseStart_7932967 : Nat := 118140960795 + 7932967 * 2 ^ 59
def prefixEnd_7932967 : Nat := 4983230072969 + 3 ^ 40 * 7932967 * 2
def baseEnd_7932967 : Nat := 452602787472885440425495

theorem tailTrace_7932967 : CollatzResearch.WordTrace tailWord_7932967 prefixEnd_7932967 452602787472885440425495 := by
  unfold tailWord_7932967
  simp only [CollatzResearch.WordTrace]
  refine ⟨289339076651222876744157155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192892717767481917829438103 289339076651222876744157155)
  ·
    refine ⟨434008614976834315116235733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289339076651222876744157155 434008614976834315116235733)
    ·
      refine ⟨10172076913519554260536775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 434008614976834315116235733 10172076913519554260536775)
      ·
        refine ⟨15258115370279331390805163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10172076913519554260536775 15258115370279331390805163)
        ·
          refine ⟨22887173055418997086207745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15258115370279331390805163 22887173055418997086207745)
          ·
            refine ⟨17165379791564247814655809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22887173055418997086207745 17165379791564247814655809)
            ·
              refine ⟨12874034843673185860991857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17165379791564247814655809 12874034843673185860991857)
              ·
                refine ⟨9655526132754889395743893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12874034843673185860991857 9655526132754889395743893)
                ·
                  refine ⟨452602787472885440425495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9655526132754889395743893 452602787472885440425495)
                  ·
                    rfl

theorem cell23_7932967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 6].length) (baseStart_7932967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7932967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7932967 prefixEnd_7932967 := by exact prefixLift 7932967
  have htrace : WordTrace (prefixWord ++ tailWord_7932967) baseStart_7932967 baseEnd_7932967 := by
    simpa [prefixWord, tailWord_7932967, baseEnd_7932967] using wordTrace_append hprefix tailTrace_7932967
  have hstable : (prefixWord ++ tailWord_7932967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7932967).length < 2 ^ (prefixWord ++ tailWord_7932967).sum := by decide
  have hdescent : baseEnd_7932967 < baseStart_7932967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7932967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933000 : List Nat := [2, 1, 3, 1, 1, 1, 4, 4, 1, 1, 4]
def baseStart_7933000 : Nat := 118140960795 + 7933000 * 2 ^ 59
def prefixEnd_7933000 : Nat := 4983230072969 + 3 ^ 40 * 7933000 * 2
def baseEnd_7933000 : Nat := 4073442032117567334716803

theorem tailTrace_7933000 : CollatzResearch.WordTrace tailWord_7933000 prefixEnd_7933000 4073442032117567334716803 := by
  unfold tailWord_7933000
  simp only [CollatzResearch.WordTrace]
  refine ⟨144670140130051661690054227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192893520173402215586738969 144670140130051661690054227)
  ·
    refine ⟨217005210195077492535081341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144670140130051661690054227 217005210195077492535081341)
    ·
      refine ⟨81376953823154059700655503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217005210195077492535081341 81376953823154059700655503)
      ·
        refine ⟨122065430734731089550983255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81376953823154059700655503 122065430734731089550983255)
        ·
          refine ⟨183098146102096634326474883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122065430734731089550983255 183098146102096634326474883)
          ·
            refine ⟨274647219153144951489712325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183098146102096634326474883 274647219153144951489712325)
            ·
              refine ⟨51496353591214678404321061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274647219153144951489712325 51496353591214678404321061)
              ·
                refine ⟨9655566298352752200810199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51496353591214678404321061 9655566298352752200810199)
                ·
                  refine ⟨14483349447529128301215299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9655566298352752200810199 14483349447529128301215299)
                  ·
                    refine ⟨21725024171293692451822949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14483349447529128301215299 21725024171293692451822949)
                    ·
                      refine ⟨4073442032117567334716803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21725024171293692451822949 4073442032117567334716803)
                      ·
                        rfl

theorem cell23_7933000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_7933000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933000 prefixEnd_7933000 := by exact prefixLift 7933000
  have htrace : WordTrace (prefixWord ++ tailWord_7933000) baseStart_7933000 baseEnd_7933000 := by
    simpa [prefixWord, tailWord_7933000, baseEnd_7933000] using wordTrace_append hprefix tailTrace_7933000
  have hstable : (prefixWord ++ tailWord_7933000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933000).length < 2 ^ (prefixWord ++ tailWord_7933000).sum := by decide
  have hdescent : baseEnd_7933000 < baseStart_7933000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933010 : List Nat := [3, 2, 2, 1, 3, 1, 2, 2, 1, 6]
def baseStart_7933010 : Nat := 118140960795 + 7933010 * 2 ^ 59
def prefixEnd_7933010 : Nat := 4983230072969 + 3 ^ 40 * 7933010 * 2
def baseEnd_7933010 : Nat := 1357815722308037431863919

theorem tailTrace_7933010 : CollatzResearch.WordTrace tailWord_7933010 prefixEnd_7933010 1357815722308037431863919 := by
  unfold tailWord_7933010
  simp only [CollatzResearch.WordTrace]
  refine ⟨72335161247516773771993121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192893763326711396725314989 72335161247516773771993121)
  ·
    refine ⟨54251370935637580328994841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72335161247516773771993121 54251370935637580328994841)
    ·
      refine ⟨40688528201728185246746131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54251370935637580328994841 40688528201728185246746131)
      ·
        refine ⟨61032792302592277870119197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40688528201728185246746131 61032792302592277870119197)
        ·
          refine ⟨22887297113472104201294699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61032792302592277870119197 22887297113472104201294699)
          ·
            refine ⟨34330945670208156301942049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22887297113472104201294699 34330945670208156301942049)
            ·
              refine ⟨25748209252656117226456537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34330945670208156301942049 25748209252656117226456537)
              ·
                refine ⟨19311156939492087919842403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25748209252656117226456537 19311156939492087919842403)
                ·
                  refine ⟨28966735409238131879763605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19311156939492087919842403 28966735409238131879763605)
                  ·
                    refine ⟨1357815722308037431863919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28966735409238131879763605 1357815722308037431863919)
                    ·
                      rfl

theorem cell23_7933010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_7933010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933010 prefixEnd_7933010 := by exact prefixLift 7933010
  have htrace : WordTrace (prefixWord ++ tailWord_7933010) baseStart_7933010 baseEnd_7933010 := by
    simpa [prefixWord, tailWord_7933010, baseEnd_7933010] using wordTrace_append hprefix tailTrace_7933010
  have hstable : (prefixWord ++ tailWord_7933010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933010).length < 2 ^ (prefixWord ++ tailWord_7933010).sum := by decide
  have hdescent : baseEnd_7933010 < baseStart_7933010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933020 : List Nat := [2, 2, 4, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_7933020 : Nat := 118140960795 + 7933020 * 2 ^ 59
def prefixEnd_7933020 : Nat := 4983230072969 + 3 ^ 40 * 7933020 * 2
def baseEnd_7933020 : Nat := 4073452301730657256466711

theorem tailTrace_7933020 : CollatzResearch.WordTrace tailWord_7933020 prefixEnd_7933020 4073452301730657256466711 := by
  unfold tailWord_7933020
  simp only [CollatzResearch.WordTrace]
  refine ⟨144670504860015433397918257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192894006480020577863891009 144670504860015433397918257)
  ·
    refine ⟨108502878645011575048438693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144670504860015433397918257 108502878645011575048438693)
    ·
      refine ⟨20344289745939670321582255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108502878645011575048438693 20344289745939670321582255)
      ·
        refine ⟨30516434618909505482373383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20344289745939670321582255 30516434618909505482373383)
        ·
          refine ⟨45774651928364258223560075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30516434618909505482373383 45774651928364258223560075)
          ·
            refine ⟨68661977892546387335340113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45774651928364258223560075 68661977892546387335340113)
            ·
              refine ⟨51496483419409790501505085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68661977892546387335340113 51496483419409790501505085)
              ·
                refine ⟨19311181282278671438064407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51496483419409790501505085 19311181282278671438064407)
                ·
                  refine ⟨28966771923418007157096611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19311181282278671438064407 28966771923418007157096611)
                  ·
                    refine ⟨43450157885127010735644917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28966771923418007157096611 43450157885127010735644917)
                    ·
                      refine ⟨4073452301730657256466711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43450157885127010735644917 4073452301730657256466711)
                      ·
                        rfl

theorem cell23_7933020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_7933020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933020 prefixEnd_7933020 := by exact prefixLift 7933020
  have htrace : WordTrace (prefixWord ++ tailWord_7933020) baseStart_7933020 baseEnd_7933020 := by
    simpa [prefixWord, tailWord_7933020, baseEnd_7933020] using wordTrace_append hprefix tailTrace_7933020
  have hstable : (prefixWord ++ tailWord_7933020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933020).length < 2 ^ (prefixWord ++ tailWord_7933020).sum := by decide
  have hdescent : baseEnd_7933020 < baseStart_7933020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933034 : List Nat := [3, 1, 3, 2, 2, 1, 1, 3, 3, 2, 2]
def baseStart_7933034 : Nat := 118140960795 + 7933034 * 2 ^ 59
def prefixEnd_7933034 : Nat := 4983230072969 + 3 ^ 40 * 7933034 * 2
def baseEnd_7933034 : Nat := 4073459490459820201691647

theorem tailTrace_7933034 : CollatzResearch.WordTrace tailWord_7933034 prefixEnd_7933034 4073459490459820201691647 := by
  unfold tailWord_7933034
  simp only [CollatzResearch.WordTrace]
  refine ⟨72335380085495036796711539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192894346894653431457897437 72335380085495036796711539)
  ·
    refine ⟨108503070128242555195067309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72335380085495036796711539 108503070128242555195067309)
    ·
      refine ⟨40688651298090958198150241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108503070128242555195067309 40688651298090958198150241)
      ·
        refine ⟨30516488473568218648612681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40688651298090958198150241 30516488473568218648612681)
        ·
          refine ⟨22887366355176163986459511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30516488473568218648612681 22887366355176163986459511)
          ·
            refine ⟨34331049532764245979689267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22887366355176163986459511 34331049532764245979689267)
            ·
              refine ⟨51496574299146368969533901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34331049532764245979689267 51496574299146368969533901)
              ·
                refine ⟨19311215362179888363575213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51496574299146368969533901 19311215362179888363575213)
                ·
                  refine ⟨7241705760817458136340705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19311215362179888363575213 7241705760817458136340705)
                  ·
                    refine ⟨5431279320613093602255529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7241705760817458136340705 5431279320613093602255529)
                    ·
                      refine ⟨4073459490459820201691647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5431279320613093602255529 4073459490459820201691647)
                      ·
                        rfl

theorem cell23_7933034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_7933034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933034 prefixEnd_7933034 := by exact prefixLift 7933034
  have htrace : WordTrace (prefixWord ++ tailWord_7933034) baseStart_7933034 baseEnd_7933034 := by
    simpa [prefixWord, tailWord_7933034, baseEnd_7933034] using wordTrace_append hprefix tailTrace_7933034
  have hstable : (prefixWord ++ tailWord_7933034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933034).length < 2 ^ (prefixWord ++ tailWord_7933034).sum := by decide
  have hdescent : baseEnd_7933034 < baseStart_7933034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933057 : List Nat := [1, 2, 4, 2, 2, 3, 2, 7]
def baseStart_7933057 : Nat := 118140960795 + 7933057 * 2 ^ 59
def prefixEnd_7933057 : Nat := 4983230072969 + 3 ^ 40 * 7933057 * 2
def baseEnd_7933057 : Nat := 150869307426476800433483

theorem tailTrace_7933057 : CollatzResearch.WordTrace tailWord_7933057 prefixEnd_7933057 150869307426476800433483 := by
  unfold tailWord_7933057
  simp only [CollatzResearch.WordTrace]
  refine ⟨289342359220896822114933425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192894906147264548076622283 289342359220896822114933425)
  ·
    refine ⟨217006769415672616586200069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289342359220896822114933425 217006769415672616586200069)
    ·
      refine ⟨40688769265438615609912513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217006769415672616586200069 40688769265438615609912513)
      ·
        refine ⟨30516576949078961707434385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40688769265438615609912513 30516576949078961707434385)
        ·
          refine ⟨22887432711809221280575789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30516576949078961707434385 22887432711809221280575789)
          ·
            refine ⟨8582787266928457980215921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22887432711809221280575789 8582787266928457980215921)
            ·
              refine ⟨6437090450196343485161941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8582787266928457980215921 6437090450196343485161941)
              ·
                refine ⟨150869307426476800433483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6437090450196343485161941 150869307426476800433483)
                ·
                  rfl

theorem cell23_7933057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 7].length) (baseStart_7933057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933057 prefixEnd_7933057 := by exact prefixLift 7933057
  have htrace : WordTrace (prefixWord ++ tailWord_7933057) baseStart_7933057 baseEnd_7933057 := by
    simpa [prefixWord, tailWord_7933057, baseEnd_7933057] using wordTrace_append hprefix tailTrace_7933057
  have hstable : (prefixWord ++ tailWord_7933057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933057).length < 2 ^ (prefixWord ++ tailWord_7933057).sum := by decide
  have hdescent : baseEnd_7933057 < baseStart_7933057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933101 : List Nat := [1, 5, 2, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_7933101 : Nat := 118140960795 + 7933101 * 2 ^ 59
def prefixEnd_7933101 : Nat := 4983230072969 + 3 ^ 40 * 7933101 * 2
def baseEnd_7933101 : Nat := 4073493893663671439553839

theorem tailTrace_7933101 : CollatzResearch.WordTrace tailWord_7933101 prefixEnd_7933101 4073493893663671439553839 := by
  unfold tailWord_7933101
  simp only [CollatzResearch.WordTrace]
  refine ⟨289343964032737417629535157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192895976021824945086356771 289343964032737417629535157)
  ·
    refine ⟨27125996628069132902768921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289343964032737417629535157 27125996628069132902768921)
    ·
      refine ⟨20344497471051849677076691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27125996628069132902768921 20344497471051849677076691)
      ·
        refine ⟨30516746206577774515615037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20344497471051849677076691 30516746206577774515615037)
        ·
          refine ⟨11443779827466665443355639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30516746206577774515615037 11443779827466665443355639)
          ·
            refine ⟨17165669741199998165033459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11443779827466665443355639 17165669741199998165033459)
            ·
              refine ⟨25748504611799997247550189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17165669741199998165033459 25748504611799997247550189)
              ·
                refine ⟨9655689229424998967831321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25748504611799997247550189 9655689229424998967831321)
                ·
                  refine ⟨7241766922068749225873491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9655689229424998967831321 7241766922068749225873491)
                  ·
                    refine ⟨10862650383103123838810237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7241766922068749225873491 10862650383103123838810237)
                    ·
                      refine ⟨4073493893663671439553839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10862650383103123838810237 4073493893663671439553839)
                      ·
                        rfl

theorem cell23_7933101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_7933101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933101 prefixEnd_7933101 := by exact prefixLift 7933101
  have htrace : WordTrace (prefixWord ++ tailWord_7933101) baseStart_7933101 baseEnd_7933101 := by
    simpa [prefixWord, tailWord_7933101, baseEnd_7933101] using wordTrace_append hprefix tailTrace_7933101
  have hstable : (prefixWord ++ tailWord_7933101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933101).length < 2 ^ (prefixWord ++ tailWord_7933101).sum := by decide
  have hdescent : baseEnd_7933101 < baseStart_7933101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933123 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 7]
def baseStart_7933123 : Nat := 118140960795 + 7933123 * 2 ^ 59
def prefixEnd_7933123 : Nat := 4983230072969 + 3 ^ 40 * 7933123 * 2
def baseEnd_7933123 : Nat := 4073505190238070353478737

theorem tailTrace_7933123 : CollatzResearch.WordTrace tailWord_7933123 prefixEnd_7933123 4073505190238070353478737 := by
  unfold tailWord_7933123
  simp only [CollatzResearch.WordTrace]
  refine ⟨289344766438657715386836023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192896510959105143591224015 289344766438657715386836023)
  ·
    refine ⟨434017149657986573080254035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289344766438657715386836023 434017149657986573080254035)
    ·
      refine ⟨651025724486979859620381053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434017149657986573080254035 651025724486979859620381053)
      ·
        refine ⟨244134646682617447357642895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 651025724486979859620381053 244134646682617447357642895)
        ·
          refine ⟨366201970023926171036464343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244134646682617447357642895 366201970023926171036464343)
          ·
            refine ⟨549302955035889256554696515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366201970023926171036464343 549302955035889256554696515)
            ·
              refine ⟨823954432553833884832044773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549302955035889256554696515 823954432553833884832044773)
              ·
                refine ⟨154491456103843853406008395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 823954432553833884832044773 154491456103843853406008395)
                ·
                  refine ⟨231737184155765780109012593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154491456103843853406008395 231737184155765780109012593)
                  ·
                    refine ⟨173802888116824335081759445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 231737184155765780109012593 173802888116824335081759445)
                    ·
                      refine ⟨4073505190238070353478737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173802888116824335081759445 4073505190238070353478737)
                      ·
                        rfl

theorem cell23_7933123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_7933123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933123 prefixEnd_7933123 := by exact prefixLift 7933123
  have htrace : WordTrace (prefixWord ++ tailWord_7933123) baseStart_7933123 baseEnd_7933123 := by
    simpa [prefixWord, tailWord_7933123, baseEnd_7933123] using wordTrace_append hprefix tailTrace_7933123
  have hstable : (prefixWord ++ tailWord_7933123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933123).length < 2 ^ (prefixWord ++ tailWord_7933123).sum := by decide
  have hdescent : baseEnd_7933123 < baseStart_7933123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933141 : List Nat := [1, 3, 2, 4, 1, 1, 1, 4, 2, 2, 2]
def baseStart_7933141 : Nat := 118140960795 + 7933141 * 2 ^ 59
def prefixEnd_7933141 : Nat := 4983230072969 + 3 ^ 40 * 7933141 * 2
def baseEnd_7933141 : Nat := 4073514432889851283053655

theorem tailTrace_7933141 : CollatzResearch.WordTrace tailWord_7933141 prefixEnd_7933141 4073514432889851283053655 := by
  unfold tailWord_7933141
  simp only [CollatzResearch.WordTrace]
  refine ⟨289345422952592504460991277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192896948635061669640660851 289345422952592504460991277)
  ·
    refine ⟨108504533607222189172871729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289345422952592504460991277 108504533607222189172871729)
    ·
      refine ⟨81378400205416641879653797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108504533607222189172871729 81378400205416641879653797)
      ·
        refine ⟨15258450038515620352435087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81378400205416641879653797 15258450038515620352435087)
        ·
          refine ⟨22887675057773430528652631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15258450038515620352435087 22887675057773430528652631)
          ·
            refine ⟨34331512586660145792978947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22887675057773430528652631 34331512586660145792978947)
            ·
              refine ⟨51497268879990218689468421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34331512586660145792978947 51497268879990218689468421)
              ·
                refine ⟨9655737914998166004275329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51497268879990218689468421 9655737914998166004275329)
                ·
                  refine ⟨7241803436248624503206497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9655737914998166004275329 7241803436248624503206497)
                  ·
                    refine ⟨5431352577186468377404873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7241803436248624503206497 5431352577186468377404873)
                    ·
                      refine ⟨4073514432889851283053655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5431352577186468377404873 4073514432889851283053655)
                      ·
                        rfl

theorem cell23_7933141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_7933141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933141 prefixEnd_7933141 := by exact prefixLift 7933141
  have htrace : WordTrace (prefixWord ++ tailWord_7933141) baseStart_7933141 baseEnd_7933141 := by
    simpa [prefixWord, tailWord_7933141, baseEnd_7933141] using wordTrace_append hprefix tailTrace_7933141
  have hstable : (prefixWord ++ tailWord_7933141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933141).length < 2 ^ (prefixWord ++ tailWord_7933141).sum := by decide
  have hdescent : baseEnd_7933141 < baseStart_7933141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933160 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 1, 7]
def baseStart_7933160 : Nat := 118140960795 + 7933160 * 2 ^ 59
def prefixEnd_7933160 : Nat := 4983230072969 + 3 ^ 40 * 7933160 * 2
def baseEnd_7933160 : Nat := 1357841396340762236238689

theorem tailTrace_7933160 : CollatzResearch.WordTrace tailWord_7933160 prefixEnd_7933160 1357841396340762236238689 := by
  unfold tailWord_7933160
  simp only [CollatzResearch.WordTrace]
  refine ⟨144673057969761835352966467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192897410626349113803955289 144673057969761835352966467)
  ·
    refine ⟨217009586954642753029449701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144673057969761835352966467 217009586954642753029449701)
    ·
      refine ⟨40689297553995516193021819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217009586954642753029449701 40689297553995516193021819)
      ·
        refine ⟨61033946330993274289532729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40689297553995516193021819 61033946330993274289532729)
        ·
          refine ⟨45775459748244955717149547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61033946330993274289532729 45775459748244955717149547)
          ·
            refine ⟨68663189622367433575724321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45775459748244955717149547 68663189622367433575724321)
            ·
              refine ⟨51497392216775575181793241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68663189622367433575724321 51497392216775575181793241)
              ·
                refine ⟨38623044162581681386344931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51497392216775575181793241 38623044162581681386344931)
                ·
                  refine ⟨57934566243872522079517397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38623044162581681386344931 57934566243872522079517397)
                  ·
                    refine ⟨1357841396340762236238689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57934566243872522079517397 1357841396340762236238689)
                    ·
                      rfl

theorem cell23_7933160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_7933160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933160 prefixEnd_7933160 := by exact prefixLift 7933160
  have htrace : WordTrace (prefixWord ++ tailWord_7933160) baseStart_7933160 baseEnd_7933160 := by
    simpa [prefixWord, tailWord_7933160, baseEnd_7933160] using wordTrace_append hprefix tailTrace_7933160
  have hstable : (prefixWord ++ tailWord_7933160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933160).length < 2 ^ (prefixWord ++ tailWord_7933160).sum := by decide
  have hdescent : baseEnd_7933160 < baseStart_7933160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933224 : List Nat := [2, 1, 5, 1, 2, 1, 2, 2, 3, 4]
def baseStart_7933224 : Nat := 118140960795 + 7933224 * 2 ^ 59
def prefixEnd_7933224 : Nat := 4983230072969 + 3 ^ 40 * 7933224 * 2
def baseEnd_7933224 : Nat := 1357852350594724819438591

theorem tailTrace_7933224 : CollatzResearch.WordTrace tailWord_7933224 prefixEnd_7933224 1357852350594724819438591 := by
  unfold tailWord_7933224
  simp only [CollatzResearch.WordTrace]
  refine ⟨144674225105645904818131363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192898966807527873090841817 144674225105645904818131363)
  ·
    refine ⟨217011337658468857227197045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144674225105645904818131363 217011337658468857227197045)
    ·
      refine ⟨20344812905481455365049723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217011337658468857227197045 20344812905481455365049723)
      ·
        refine ⟨30517219358222183047574585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20344812905481455365049723 30517219358222183047574585)
        ·
          refine ⟨22887914518666637285680939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30517219358222183047574585 22887914518666637285680939)
          ·
            refine ⟨34331871777999955928521409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22887914518666637285680939 34331871777999955928521409)
            ·
              refine ⟨25748903833499966946391057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34331871777999955928521409 25748903833499966946391057)
              ·
                refine ⟨19311677875124975209793293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25748903833499966946391057 19311677875124975209793293)
                ·
                  refine ⟨7241879203171865703672485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19311677875124975209793293 7241879203171865703672485)
                  ·
                    refine ⟨1357852350594724819438591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7241879203171865703672485 1357852350594724819438591)
                    ·
                      rfl

theorem cell23_7933224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_7933224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933224 prefixEnd_7933224 := by exact prefixLift 7933224
  have htrace : WordTrace (prefixWord ++ tailWord_7933224) baseStart_7933224 baseEnd_7933224 := by
    simpa [prefixWord, tailWord_7933224, baseEnd_7933224] using wordTrace_append hprefix tailTrace_7933224
  have hstable : (prefixWord ++ tailWord_7933224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933224).length < 2 ^ (prefixWord ++ tailWord_7933224).sum := by decide
  have hdescent : baseEnd_7933224 < baseStart_7933224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933284 : List Nat := [2, 3, 1, 1, 3, 2, 3, 2, 1, 5]
def baseStart_7933284 : Nat := 118140960795 + 7933284 * 2 ^ 59
def prefixEnd_7933284 : Nat := 4983230072969 + 3 ^ 40 * 7933284 * 2
def baseEnd_7933284 : Nat := 1357862620207814741188499

theorem tailTrace_7933284 : CollatzResearch.WordTrace tailWord_7933284 prefixEnd_7933284 1357862620207814741188499 := by
  unfold tailWord_7933284
  simp only [CollatzResearch.WordTrace]
  refine ⟨144675319295537219941723453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192900425727382959922297937 144675319295537219941723453)
  ·
    refine ⟨54253244735826457478146295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144675319295537219941723453 54253244735826457478146295)
    ·
      refine ⟨81379867103739686217219443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54253244735826457478146295 81379867103739686217219443)
      ·
        refine ⟨122069800655609529325829165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81379867103739686217219443 122069800655609529325829165)
        ·
          refine ⟨45776175245853573497185937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122069800655609529325829165 45776175245853573497185937)
          ·
            refine ⟨34332131434390180122889453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45776175245853573497185937 34332131434390180122889453)
            ·
              refine ⟨12874549287896317546083545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34332131434390180122889453 12874549287896317546083545)
              ·
                refine ⟨9655911965922238159562659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12874549287896317546083545 9655911965922238159562659)
                ·
                  refine ⟨14483867948883357239343989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9655911965922238159562659 14483867948883357239343989)
                  ·
                    refine ⟨1357862620207814741188499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14483867948883357239343989 1357862620207814741188499)
                    ·
                      rfl

theorem cell23_7933284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_7933284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933284 prefixEnd_7933284 := by exact prefixLift 7933284
  have htrace : WordTrace (prefixWord ++ tailWord_7933284) baseStart_7933284 baseEnd_7933284 := by
    simpa [prefixWord, tailWord_7933284, baseEnd_7933284] using wordTrace_append hprefix tailTrace_7933284
  have hstable : (prefixWord ++ tailWord_7933284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933284).length < 2 ^ (prefixWord ++ tailWord_7933284).sum := by decide
  have hdescent : baseEnd_7933284 < baseStart_7933284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933297 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 6, 4]
def baseStart_7933297 : Nat := 118140960795 + 7933297 * 2 ^ 59
def prefixEnd_7933297 : Nat := 4983230072969 + 3 ^ 40 * 7933297 * 2
def baseEnd_7933297 : Nat := 1357864845290650890900979

theorem tailTrace_7933297 : CollatzResearch.WordTrace tailWord_7933297 prefixEnd_7933297 1357864845290650890900979 := by
  unfold tailWord_7933297
  simp only [CollatzResearch.WordTrace]
  refine ⟨289351112740027343103670145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192900741826684895402446763 289351112740027343103670145)
  ·
    refine ⟨217013334555020507327752609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289351112740027343103670145 217013334555020507327752609)
    ·
      refine ⟨162760000916265380495814457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217013334555020507327752609 162760000916265380495814457)
      ·
        refine ⟨122070000687199035371860843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162760000916265380495814457 122070000687199035371860843)
        ·
          refine ⟨183105001030798553057791265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122070000687199035371860843 183105001030798553057791265)
          ·
            refine ⟨137328750773098914793343449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183105001030798553057791265 137328750773098914793343449)
            ·
              refine ⟨102996563079824186095007587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137328750773098914793343449 102996563079824186095007587)
              ·
                refine ⟨154494844619736279142511381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102996563079824186095007587 154494844619736279142511381)
                ·
                  refine ⟨7241945841550138084805221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154494844619736279142511381 7241945841550138084805221)
                  ·
                    refine ⟨1357864845290650890900979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7241945841550138084805221 1357864845290650890900979)
                    ·
                      rfl

theorem cell23_7933297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_7933297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933297 prefixEnd_7933297 := by exact prefixLift 7933297
  have htrace : WordTrace (prefixWord ++ tailWord_7933297) baseStart_7933297 baseEnd_7933297 := by
    simpa [prefixWord, tailWord_7933297, baseEnd_7933297] using wordTrace_append hprefix tailTrace_7933297
  have hstable : (prefixWord ++ tailWord_7933297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933297).length < 2 ^ (prefixWord ++ tailWord_7933297).sum := by decide
  have hdescent : baseEnd_7933297 < baseStart_7933297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933315 : List Nat := [1, 1, 1, 3, 5, 3, 2, 2, 1, 1, 3]
def baseStart_7933315 : Nat := 118140960795 + 7933315 * 2 ^ 59
def prefixEnd_7933315 : Nat := 4983230072969 + 3 ^ 40 * 7933315 * 2
def baseEnd_7933315 : Nat := 4073603778523733602277855

theorem tailTrace_7933315 : CollatzResearch.WordTrace tailWord_7933315 prefixEnd_7933315 4073603778523733602277855 := by
  unfold tailWord_7933315
  simp only [CollatzResearch.WordTrace]
  refine ⟨289351769253962132177825399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192901179502641421451883599 289351769253962132177825399)
  ·
    refine ⟨434027653880943198266738099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289351769253962132177825399 434027653880943198266738099)
    ·
      refine ⟨651041480821414797400107149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434027653880943198266738099 651041480821414797400107149)
      ·
        refine ⟨244140555308030549025040181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 651041480821414797400107149 244140555308030549025040181)
        ·
          refine ⟨22888177060127863971097517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 244140555308030549025040181 22888177060127863971097517)
          ·
            refine ⟨8583066397547948989161569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22888177060127863971097517 8583066397547948989161569)
            ·
              refine ⟨6437299798160961741871177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8583066397547948989161569 6437299798160961741871177)
              ·
                refine ⟨4827974848620721306403383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6437299798160961741871177 4827974848620721306403383)
                ·
                  refine ⟨7241962272931081959605075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4827974848620721306403383 7241962272931081959605075)
                  ·
                    refine ⟨10862943409396622939407613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7241962272931081959605075 10862943409396622939407613)
                    ·
                      refine ⟨4073603778523733602277855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10862943409396622939407613 4073603778523733602277855)
                      ·
                        rfl

theorem cell23_7933315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 1, 1, 3].length) (baseStart_7933315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933315 prefixEnd_7933315 := by exact prefixLift 7933315
  have htrace : WordTrace (prefixWord ++ tailWord_7933315) baseStart_7933315 baseEnd_7933315 := by
    simpa [prefixWord, tailWord_7933315, baseEnd_7933315] using wordTrace_append hprefix tailTrace_7933315
  have hstable : (prefixWord ++ tailWord_7933315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933315).length < 2 ^ (prefixWord ++ tailWord_7933315).sum := by decide
  have hdescent : baseEnd_7933315 < baseStart_7933315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933342 : List Nat := [4, 3, 1, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_7933342 : Nat := 118140960795 + 7933342 * 2 ^ 59
def prefixEnd_7933342 : Nat := 4983230072969 + 3 ^ 40 * 7933342 * 2
def baseEnd_7933342 : Nat := 4073617642501404996640231

theorem tailTrace_7933342 : CollatzResearch.WordTrace tailWord_7933342 prefixEnd_7933342 4073617642501404996640231 := by
  unfold tailWord_7933342
  simp only [CollatzResearch.WordTrace]
  refine ⟨36169094253108039473632285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192901836016576210526038853 36169094253108039473632285)
  ·
    refine ⟨13563410344915514802612107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36169094253108039473632285 13563410344915514802612107)
    ·
      refine ⟨20345115517373272203918161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13563410344915514802612107 20345115517373272203918161)
      ·
        refine ⟨15258836638029954152938621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20345115517373272203918161 15258836638029954152938621)
        ·
          refine ⟨5722063739261232807351983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15258836638029954152938621 5722063739261232807351983)
          ·
            refine ⟨8583095608891849211027975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5722063739261232807351983 8583095608891849211027975)
            ·
              refine ⟨12874643413337773816541963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8583095608891849211027975 12874643413337773816541963)
              ·
                refine ⟨19311965120006660724812945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12874643413337773816541963 19311965120006660724812945)
                ·
                  refine ⟨14483973840004995543609709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19311965120006660724812945 14483973840004995543609709)
                  ·
                    refine ⟨5431490190001873328853641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14483973840004995543609709 5431490190001873328853641)
                    ·
                      refine ⟨4073617642501404996640231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5431490190001873328853641 4073617642501404996640231)
                      ·
                        rfl

theorem cell23_7933342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_7933342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933342 prefixEnd_7933342 := by exact prefixLift 7933342
  have htrace : WordTrace (prefixWord ++ tailWord_7933342) baseStart_7933342 baseEnd_7933342 := by
    simpa [prefixWord, tailWord_7933342, baseEnd_7933342] using wordTrace_append hprefix tailTrace_7933342
  have hstable : (prefixWord ++ tailWord_7933342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933342).length < 2 ^ (prefixWord ++ tailWord_7933342).sum := by decide
  have hdescent : baseEnd_7933342 < baseStart_7933342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933387 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 2, 6]
def baseStart_7933387 : Nat := 118140960795 + 7933387 * 2 ^ 59
def prefixEnd_7933387 : Nat := 4983230072969 + 3 ^ 40 * 7933387 * 2
def baseEnd_7933387 : Nat := 1357880249710285773525841

theorem tailTrace_7933387 : CollatzResearch.WordTrace tailWord_7933387 prefixEnd_7933387 1357880249710285773525841 := by
  unfold tailWord_7933387
  simp only [CollatzResearch.WordTrace]
  refine ⟨289354395309701288474446415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192902930206467525649630943 289354395309701288474446415)
  ·
    refine ⟨434031592964551932711669623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289354395309701288474446415 434031592964551932711669623)
    ·
      refine ⟨651047389446827899067504435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434031592964551932711669623 651047389446827899067504435)
      ·
        refine ⟨976571084170241848601256653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651047389446827899067504435 976571084170241848601256653)
        ·
          refine ⟨366214156563840693225471245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 976571084170241848601256653 366214156563840693225471245)
          ·
            refine ⟨137330308711440259959551717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366214156563840693225471245 137330308711440259959551717)
            ·
              refine ⟨25749432883395048742415947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137330308711440259959551717 25749432883395048742415947)
              ·
                refine ⟨38624149325092573113623921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25749432883395048742415947 38624149325092573113623921)
                ·
                  refine ⟨28968111993819429835217941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38624149325092573113623921 28968111993819429835217941)
                  ·
                    refine ⟨1357880249710285773525841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28968111993819429835217941 1357880249710285773525841)
                    ·
                      rfl

theorem cell23_7933387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 6].length) (baseStart_7933387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933387 prefixEnd_7933387 := by exact prefixLift 7933387
  have htrace : WordTrace (prefixWord ++ tailWord_7933387) baseStart_7933387 baseEnd_7933387 := by
    simpa [prefixWord, tailWord_7933387, baseEnd_7933387] using wordTrace_append hprefix tailTrace_7933387
  have hstable : (prefixWord ++ tailWord_7933387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933387).length < 2 ^ (prefixWord ++ tailWord_7933387).sum := by decide
  have hdescent : baseEnd_7933387 < baseStart_7933387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933457 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 7]
def baseStart_7933457 : Nat := 118140960795 + 7933457 * 2 ^ 59
def prefixEnd_7933457 : Nat := 4983230072969 + 3 ^ 40 * 7933457 * 2
def baseEnd_7933457 : Nat := 4073676692776672046702201

theorem tailTrace_7933457 : CollatzResearch.WordTrace tailWord_7933457 prefixEnd_7933457 4073676692776672046702201 := by
  unfold tailWord_7933457
  simp only [CollatzResearch.WordTrace]
  refine ⟨289356948419447690429494625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192904632279631793619663083 289356948419447690429494625)
  ·
    refine ⟨217017711314585767822120969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289356948419447690429494625 217017711314585767822120969)
    ·
      refine ⟨162763283485939325866590727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217017711314585767822120969 162763283485939325866590727)
      ·
        refine ⟨244144925228908988799886091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162763283485939325866590727 244144925228908988799886091)
        ·
          refine ⟨366217387843363483199829137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244144925228908988799886091 366217387843363483199829137)
          ·
            refine ⟨274663040882522612399871853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366217387843363483199829137 274663040882522612399871853)
            ·
              refine ⟨102998640330945979649951945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274663040882522612399871853 102998640330945979649951945)
              ·
                refine ⟨77248980248209484737463959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102998640330945979649951945 77248980248209484737463959)
                ·
                  refine ⟨115873470372314227106195939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77248980248209484737463959 115873470372314227106195939)
                  ·
                    refine ⟨173810205558471340659293909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115873470372314227106195939 173810205558471340659293909)
                    ·
                      refine ⟨4073676692776672046702201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173810205558471340659293909 4073676692776672046702201)
                      ·
                        rfl

theorem cell23_7933457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_7933457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933457 prefixEnd_7933457 := by exact prefixLift 7933457
  have htrace : WordTrace (prefixWord ++ tailWord_7933457) baseStart_7933457 baseEnd_7933457 := by
    simpa [prefixWord, tailWord_7933457, baseEnd_7933457] using wordTrace_append hprefix tailTrace_7933457
  have hstable : (prefixWord ++ tailWord_7933457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933457).length < 2 ^ (prefixWord ++ tailWord_7933457).sum := by decide
  have hdescent : baseEnd_7933457 < baseStart_7933457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933474 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_7933474 : Nat := 118140960795 + 7933474 * 2 ^ 59
def prefixEnd_7933474 : Nat := 4983230072969 + 3 ^ 40 * 7933474 * 2
def baseEnd_7933474 : Nat := 4073685421947798480189623

theorem tailTrace_7933474 : CollatzResearch.WordTrace tailWord_7933474 prefixEnd_7933474 4073685421947798480189623 := by
  unfold tailWord_7933474
  simp only [CollatzResearch.WordTrace]
  refine ⟨72339392115096525583215869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192905045640257401555242317 72339392115096525583215869)
  ·
    refine ⟨27127272043161197093705951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72339392115096525583215869 27127272043161197093705951)
    ·
      refine ⟨40690908064741795640558927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27127272043161197093705951 40690908064741795640558927)
      ·
        refine ⟨61036362097112693460838391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40690908064741795640558927 61036362097112693460838391)
        ·
          refine ⟨91554543145669040191257587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61036362097112693460838391 91554543145669040191257587)
          ·
            refine ⟨137331814718503560286886381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91554543145669040191257587 137331814718503560286886381)
            ·
              refine ⟨51499430519438835107582393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137331814718503560286886381 51499430519438835107582393)
              ·
                refine ⟨38624572889579126330686795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51499430519438835107582393 38624572889579126330686795)
                ·
                  refine ⟨57936859334368689496030193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38624572889579126330686795 57936859334368689496030193)
                  ·
                    refine ⟨43452644500776517122022645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57936859334368689496030193 43452644500776517122022645)
                    ·
                      refine ⟨4073685421947798480189623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43452644500776517122022645 4073685421947798480189623)
                      ·
                        rfl

theorem cell23_7933474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_7933474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933474 prefixEnd_7933474 := by exact prefixLift 7933474
  have htrace : WordTrace (prefixWord ++ tailWord_7933474) baseStart_7933474 baseEnd_7933474 := by
    simpa [prefixWord, tailWord_7933474, baseEnd_7933474] using wordTrace_append hprefix tailTrace_7933474
  have hstable : (prefixWord ++ tailWord_7933474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933474).length < 2 ^ (prefixWord ++ tailWord_7933474).sum := by decide
  have hdescent : baseEnd_7933474 < baseStart_7933474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933504 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 3]
def baseStart_7933504 : Nat := 118140960795 + 7933504 * 2 ^ 59
def prefixEnd_7933504 : Nat := 4983230072969 + 3 ^ 40 * 7933504 * 2
def baseEnd_7933504 : Nat := 4073700826367433362814485

theorem tailTrace_7933504 : CollatzResearch.WordTrace tailWord_7933504 prefixEnd_7933504 4073700826367433362814485 := by
  unfold tailWord_7933504
  simp only [CollatzResearch.WordTrace]
  refine ⟨144679331325138708728227783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192905775100184944970970377 144679331325138708728227783)
  ·
    refine ⟨217018996987708063092341675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144679331325138708728227783 217018996987708063092341675)
    ·
      refine ⟨325528495481562094638512513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217018996987708063092341675 325528495481562094638512513)
      ·
        refine ⟨244146371611171570978884385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325528495481562094638512513 244146371611171570978884385)
        ·
          refine ⟨183109778708378678234163289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244146371611171570978884385 183109778708378678234163289)
          ·
            refine ⟨137332334031284008675622467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183109778708378678234163289 137332334031284008675622467)
            ·
              refine ⟨205998501046926013013433701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137332334031284008675622467 205998501046926013013433701)
              ·
                refine ⟨38624718946298627440018819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205998501046926013013433701 38624718946298627440018819)
                ·
                  refine ⟨57937078419447941160028229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38624718946298627440018819 57937078419447941160028229)
                  ·
                    refine ⟨10863202203646488967505293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57937078419447941160028229 10863202203646488967505293)
                    ·
                      refine ⟨4073700826367433362814485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10863202203646488967505293 4073700826367433362814485)
                      ·
                        rfl

theorem cell23_7933504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_7933504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933504 prefixEnd_7933504 := by exact prefixLift 7933504
  have htrace : WordTrace (prefixWord ++ tailWord_7933504) baseStart_7933504 baseEnd_7933504 := by
    simpa [prefixWord, tailWord_7933504, baseEnd_7933504] using wordTrace_append hprefix tailTrace_7933504
  have hstable : (prefixWord ++ tailWord_7933504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933504).length < 2 ^ (prefixWord ++ tailWord_7933504).sum := by decide
  have hdescent : baseEnd_7933504 < baseStart_7933504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933507 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 12]
def baseStart_7933507 : Nat := 118140960795 + 7933507 * 2 ^ 59
def prefixEnd_7933507 : Nat := 4983230072969 + 3 ^ 40 * 7933507 * 2
def baseEnd_7933507 : Nat := 452633596312155205675219

theorem tailTrace_7933507 : CollatzResearch.WordTrace tailWord_7933507 prefixEnd_7933507 452633596312155205675219 := by
  unfold tailWord_7933507
  simp only [CollatzResearch.WordTrace]
  refine ⟨289358772069266548968814775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192905848046177699312543183 289358772069266548968814775)
  ·
    refine ⟨434038158103899823453222163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289358772069266548968814775 434038158103899823453222163)
    ·
      refine ⟨651057237155849735179833245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434038158103899823453222163 651057237155849735179833245)
      ·
        refine ⟨244146463933443650692437467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 651057237155849735179833245 244146463933443650692437467)
        ·
          refine ⟨366219695900165476038656201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244146463933443650692437467 366219695900165476038656201)
          ·
            refine ⟨274664771925124107028992151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366219695900165476038656201 274664771925124107028992151)
            ·
              refine ⟨411997157887686160543488227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274664771925124107028992151 411997157887686160543488227)
              ·
                refine ⟨617995736831529240815232341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411997157887686160543488227 617995736831529240815232341)
                ·
                  refine ⟨452633596312155205675219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 617995736831529240815232341 452633596312155205675219)
                  ·
                    rfl

theorem cell23_7933507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 12].length) (baseStart_7933507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933507 prefixEnd_7933507 := by exact prefixLift 7933507
  have htrace : WordTrace (prefixWord ++ tailWord_7933507) baseStart_7933507 baseEnd_7933507 := by
    simpa [prefixWord, tailWord_7933507, baseEnd_7933507] using wordTrace_append hprefix tailTrace_7933507
  have hstable : (prefixWord ++ tailWord_7933507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933507).length < 2 ^ (prefixWord ++ tailWord_7933507).sum := by decide
  have hdescent : baseEnd_7933507 < baseStart_7933507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933524 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 8]
def baseStart_7933524 : Nat := 118140960795 + 7933524 * 2 ^ 59
def prefixEnd_7933524 : Nat := 4983230072969 + 3 ^ 40 * 7933524 * 2
def baseEnd_7933524 : Nat := 452634566220058142729377

theorem tailTrace_7933524 : CollatzResearch.WordTrace tailWord_7933524 prefixEnd_7933524 452634566220058142729377 := by
  unfold tailWord_7933524
  simp only [CollatzResearch.WordTrace]
  refine ⟨144679696055102480436091813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192906261406803307248122417 144679696055102480436091813)
  ·
    refine ⟨27127443010331715081767215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144679696055102480436091813 27127443010331715081767215)
    ·
      refine ⟨40691164515497572622650823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27127443010331715081767215 40691164515497572622650823)
      ·
        refine ⟨61036746773246358933976235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40691164515497572622650823 61036746773246358933976235)
        ·
          refine ⟨91555120159869538400964353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61036746773246358933976235 91555120159869538400964353)
          ·
            refine ⟨68666340119902153800723265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91555120159869538400964353 68666340119902153800723265)
            ·
              refine ⟨51499755089926615350542449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68666340119902153800723265 51499755089926615350542449)
              ·
                refine ⟨38624816317444961512906837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51499755089926615350542449 38624816317444961512906837)
                ·
                  refine ⟨452634566220058142729377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38624816317444961512906837 452634566220058142729377)
                  ·
                    rfl

theorem cell23_7933524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_7933524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933524 prefixEnd_7933524 := by exact prefixLift 7933524
  have htrace : WordTrace (prefixWord ++ tailWord_7933524) baseStart_7933524 baseEnd_7933524 := by
    simpa [prefixWord, tailWord_7933524, baseEnd_7933524] using wordTrace_append hprefix tailTrace_7933524
  have hstable : (prefixWord ++ tailWord_7933524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933524).length < 2 ^ (prefixWord ++ tailWord_7933524).sum := by decide
  have hdescent : baseEnd_7933524 < baseStart_7933524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933541 : List Nat := [1, 3, 1, 3, 3, 1, 3, 2, 6]
def baseStart_7933541 : Nat := 118140960795 + 7933541 * 2 ^ 59
def prefixEnd_7933541 : Nat := 4983230072969 + 3 ^ 40 * 7933541 * 2
def baseEnd_7933541 : Nat := 452635536127961079783535

theorem tailTrace_7933541 : CollatzResearch.WordTrace tailWord_7933541 prefixEnd_7933541 452635536127961079783535 := by
  unfold tailWord_7933541
  simp only [CollatzResearch.WordTrace]
  refine ⟨289360012151143372775552477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192906674767428915183701651 289360012151143372775552477)
  ·
    refine ⟨108510004556678764790832179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289360012151143372775552477 108510004556678764790832179)
    ·
      refine ⟨162765006835018147186248269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108510004556678764790832179 162765006835018147186248269)
      ·
        refine ⟨61036877563131805194843101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162765006835018147186248269 61036877563131805194843101)
        ·
          refine ⟨22888829086174426948066163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61036877563131805194843101 22888829086174426948066163)
          ·
            refine ⟨34333243629261640422099245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22888829086174426948066163 34333243629261640422099245)
            ·
              refine ⟨12874966360973115158287217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34333243629261640422099245 12874966360973115158287217)
              ·
                refine ⟨9656224770729836368715413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12874966360973115158287217 9656224770729836368715413)
                ·
                  refine ⟨452635536127961079783535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9656224770729836368715413 452635536127961079783535)
                  ·
                    rfl

theorem cell23_7933541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 6].length) (baseStart_7933541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933541 prefixEnd_7933541 := by exact prefixLift 7933541
  have htrace : WordTrace (prefixWord ++ tailWord_7933541) baseStart_7933541 baseEnd_7933541 := by
    simpa [prefixWord, tailWord_7933541, baseEnd_7933541] using wordTrace_append hprefix tailTrace_7933541
  have hstable : (prefixWord ++ tailWord_7933541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933541).length < 2 ^ (prefixWord ++ tailWord_7933541).sum := by decide
  have hdescent : baseEnd_7933541 < baseStart_7933541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933561 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 3, 5, 2]
def baseStart_7933561 : Nat := 118140960795 + 7933561 * 2 ^ 59
def prefixEnd_7933561 : Nat := 4983230072969 + 3 ^ 40 * 7933561 * 2
def baseEnd_7933561 : Nat := 4073730094764739639801723

theorem tailTrace_7933561 : CollatzResearch.WordTrace tailWord_7933561 prefixEnd_7933561 4073730094764739639801723 := by
  unfold tailWord_7933561
  simp only [CollatzResearch.WordTrace]
  refine ⟨289360741611070916191280537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192907161074047277460853691 289360741611070916191280537)
  ·
    refine ⟨217020556208303187143460403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289360741611070916191280537 217020556208303187143460403)
    ·
      refine ⟨325530834312454780715190605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217020556208303187143460403 325530834312454780715190605)
      ·
        refine ⟨122074062867170542768196477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325530834312454780715190605 122074062867170542768196477)
        ·
          refine ⟨45777773575188953538073679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122074062867170542768196477 45777773575188953538073679)
          ·
            refine ⟨68666660362783430307110519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45777773575188953538073679 68666660362783430307110519)
            ·
              refine ⟨102999990544175145460665779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68666660362783430307110519 102999990544175145460665779)
              ·
                refine ⟨154499985816262718190998669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102999990544175145460665779 154499985816262718190998669)
                ·
                  refine ⟨57937494681098519321624501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154499985816262718190998669 57937494681098519321624501)
                  ·
                    refine ⟨5431640126352986186402297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57937494681098519321624501 5431640126352986186402297)
                    ·
                      refine ⟨4073730094764739639801723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5431640126352986186402297 4073730094764739639801723)
                      ·
                        rfl

theorem cell23_7933561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_7933561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933561 prefixEnd_7933561 := by exact prefixLift 7933561
  have htrace : WordTrace (prefixWord ++ tailWord_7933561) baseStart_7933561 baseEnd_7933561 := by
    simpa [prefixWord, tailWord_7933561, baseEnd_7933561] using wordTrace_append hprefix tailTrace_7933561
  have hstable : (prefixWord ++ tailWord_7933561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933561).length < 2 ^ (prefixWord ++ tailWord_7933561).sum := by decide
  have hdescent : baseEnd_7933561 < baseStart_7933561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933578 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 1, 5, 2]
def baseStart_7933578 : Nat := 118140960795 + 7933578 * 2 ^ 59
def prefixEnd_7933578 : Nat := 4983230072969 + 3 ^ 40 * 7933578 * 2
def baseEnd_7933578 : Nat := 4073738823935866073289145

theorem tailTrace_7933578 : CollatzResearch.WordTrace tailWord_7933578 prefixEnd_7933578 4073738823935866073289145 := by
  unfold tailWord_7933578
  simp only [CollatzResearch.WordTrace]
  refine ⟨72340340413002332023662347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192907574434672885396432925 72340340413002332023662347)
  ·
    refine ⟨108510510619503498035493521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72340340413002332023662347 108510510619503498035493521)
    ·
      refine ⟨81382882964627623526620141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108510510619503498035493521 81382882964627623526620141)
      ·
        refine ⟨30518581111735358822482553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81382882964627623526620141 30518581111735358822482553)
        ·
          refine ⟨22888935833801519116861915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30518581111735358822482553 22888935833801519116861915)
          ·
            refine ⟨34333403750702278675292873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22888935833801519116861915 34333403750702278675292873)
            ·
              refine ⟨25750052813026709006469655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34333403750702278675292873 25750052813026709006469655)
              ·
                refine ⟨38625079219540063509704483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25750052813026709006469655 38625079219540063509704483)
                ·
                  refine ⟨57937618829310095264556725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38625079219540063509704483 57937618829310095264556725)
                  ·
                    refine ⟨5431651765247821431052193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57937618829310095264556725 5431651765247821431052193)
                    ·
                      refine ⟨4073738823935866073289145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5431651765247821431052193 4073738823935866073289145)
                      ·
                        rfl

theorem cell23_7933578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_7933578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933578 prefixEnd_7933578 := by exact prefixLift 7933578
  have htrace : WordTrace (prefixWord ++ tailWord_7933578) baseStart_7933578 baseEnd_7933578 := by
    simpa [prefixWord, tailWord_7933578, baseEnd_7933578] using wordTrace_append hprefix tailTrace_7933578
  have hstable : (prefixWord ++ tailWord_7933578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933578).length < 2 ^ (prefixWord ++ tailWord_7933578).sum := by decide
  have hdescent : baseEnd_7933578 < baseStart_7933578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933584 : List Nat := [2, 1, 1, 1, 1, 1, 3, 6, 1, 6]
def baseStart_7933584 : Nat := 118140960795 + 7933584 * 2 ^ 59
def prefixEnd_7933584 : Nat := 4983230072969 + 3 ^ 40 * 7933584 * 2
def baseEnd_7933584 : Nat := 1357913968273264349938039

theorem tailTrace_7933584 : CollatzResearch.WordTrace tailWord_7933584 prefixEnd_7933584 1357913968273264349938039 := by
  unfold tailWord_7933584
  simp only [CollatzResearch.WordTrace]
  refine ⟨144680790244993795559683903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192907720326658394079578537 144680790244993795559683903)
  ·
    refine ⟨217021185367490693339525855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144680790244993795559683903 217021185367490693339525855)
    ·
      refine ⟨325531778051236040009288783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217021185367490693339525855 325531778051236040009288783)
      ·
        refine ⟨488297667076854060013933175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325531778051236040009288783 488297667076854060013933175)
        ·
          refine ⟨732446500615281090020899763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488297667076854060013933175 732446500615281090020899763)
          ·
            refine ⟨1098669750922921635031349645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732446500615281090020899763 1098669750922921635031349645)
            ·
              refine ⟨412001156596095613136756117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1098669750922921635031349645 412001156596095613136756117)
              ·
                refine ⟨19312554215441981865785443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 412001156596095613136756117 19312554215441981865785443)
                ·
                  refine ⟨28968831323162972798678165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19312554215441981865785443 28968831323162972798678165)
                  ·
                    refine ⟨1357913968273264349938039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28968831323162972798678165 1357913968273264349938039)
                    ·
                      rfl

theorem cell23_7933584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 1, 6].length) (baseStart_7933584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933584 prefixEnd_7933584 := by exact prefixLift 7933584
  have htrace : WordTrace (prefixWord ++ tailWord_7933584) baseStart_7933584 baseEnd_7933584 := by
    simpa [prefixWord, tailWord_7933584, baseEnd_7933584] using wordTrace_append hprefix tailTrace_7933584
  have hstable : (prefixWord ++ tailWord_7933584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933584).length < 2 ^ (prefixWord ++ tailWord_7933584).sum := by decide
  have hdescent : baseEnd_7933584 < baseStart_7933584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933622 : List Nat := [5, 1, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_7933622 : Nat := 118140960795 + 7933622 * 2 ^ 59
def prefixEnd_7933622 : Nat := 4983230072969 + 3 ^ 40 * 7933622 * 2
def baseEnd_7933622 : Nat := 1357920472361554633712981

theorem tailTrace_7933622 : CollatzResearch.WordTrace tailWord_7933622 prefixEnd_7933622 1357920472361554633712981 := by
  unfold tailWord_7933622
  simp only [CollatzResearch.WordTrace]
  refine ⟨18085185403990620225578195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192908644309233282406167413 18085185403990620225578195)
  ·
    refine ⟨27127778105985930338367293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18085185403990620225578195 27127778105985930338367293)
    ·
      refine ⟨10172916789744723876887735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27127778105985930338367293 10172916789744723876887735)
      ·
        refine ⟨15259375184617085815331603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10172916789744723876887735 15259375184617085815331603)
        ·
          refine ⟨22889062776925628722997405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15259375184617085815331603 22889062776925628722997405)
          ·
            refine ⟨8583398541347110771124027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22889062776925628722997405 8583398541347110771124027)
            ·
              refine ⟨12875097812020666156686041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8583398541347110771124027 12875097812020666156686041)
              ·
                refine ⟨9656323359015499617514531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12875097812020666156686041 9656323359015499617514531)
                ·
                  refine ⟨14484485038523249426271797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9656323359015499617514531 14484485038523249426271797)
                  ·
                    refine ⟨1357920472361554633712981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14484485038523249426271797 1357920472361554633712981)
                    ·
                      rfl

theorem cell23_7933622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_7933622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933622 prefixEnd_7933622 := by exact prefixLift 7933622
  have htrace : WordTrace (prefixWord ++ tailWord_7933622) baseStart_7933622 baseEnd_7933622 := by
    simpa [prefixWord, tailWord_7933622, baseEnd_7933622] using wordTrace_append hprefix tailTrace_7933622
  have hstable : (prefixWord ++ tailWord_7933622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933622).length < 2 ^ (prefixWord ++ tailWord_7933622).sum := by decide
  have hdescent : baseEnd_7933622 < baseStart_7933622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933628 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 3, 2, 3]
def baseStart_7933628 : Nat := 118140960795 + 7933628 * 2 ^ 59
def prefixEnd_7933628 : Nat := 4983230072969 + 3 ^ 40 * 7933628 * 2
def baseEnd_7933628 : Nat := 4073764497968590877663915

theorem tailTrace_7933628 : CollatzResearch.WordTrace tailWord_7933628 prefixEnd_7933628 4073764497968590877663915 := by
  unfold tailWord_7933628
  simp only [CollatzResearch.WordTrace]
  refine ⟨144681592650914093316984769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192908790201218791089313025 144681592650914093316984769)
  ·
    refine ⟨108511194488185569987738577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144681592650914093316984769 108511194488185569987738577)
    ·
      refine ⟨81383395866139177490803933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108511194488185569987738577 81383395866139177490803933)
      ·
        refine ⟨30518773449802191559051475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81383395866139177490803933 30518773449802191559051475)
        ·
          refine ⟨45778160174703287338577213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30518773449802191559051475 45778160174703287338577213)
          ·
            refine ⟨17166810065513732751966455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45778160174703287338577213 17166810065513732751966455)
            ·
              refine ⟨25750215098270599127949683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17166810065513732751966455 25750215098270599127949683)
              ·
                refine ⟨38625322647405898691924525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25750215098270599127949683 38625322647405898691924525)
                ·
                  refine ⟨14484495992777212009471697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38625322647405898691924525 14484495992777212009471697)
                  ·
                    refine ⟨10863371994582909007103773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14484495992777212009471697 10863371994582909007103773)
                    ·
                      refine ⟨4073764497968590877663915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10863371994582909007103773 4073764497968590877663915)
                      ·
                        rfl

theorem cell23_7933628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_7933628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933628 prefixEnd_7933628 := by exact prefixLift 7933628
  have htrace : WordTrace (prefixWord ++ tailWord_7933628) baseStart_7933628 baseEnd_7933628 := by
    simpa [prefixWord, tailWord_7933628, baseEnd_7933628] using wordTrace_append hprefix tailTrace_7933628
  have hstable : (prefixWord ++ tailWord_7933628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933628).length < 2 ^ (prefixWord ++ tailWord_7933628).sum := by decide
  have hdescent : baseEnd_7933628 < baseStart_7933628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933645 : List Nat := [1, 6, 2, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_7933645 : Nat := 118140960795 + 7933645 * 2 ^ 59
def prefixEnd_7933645 : Nat := 4983230072969 + 3 ^ 40 * 7933645 * 2
def baseEnd_7933645 : Nat := 4073773227139717311151337

theorem tailTrace_7933645 : CollatzResearch.WordTrace tailWord_7933645 prefixEnd_7933645 4073773227139717311151337 := by
  unfold tailWord_7933645
  simp only [CollatzResearch.WordTrace]
  refine ⟨289363805342766598537338389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192909203561844399024892259 289363805342766598537338389)
  ·
    refine ⟨13563928375442184306437737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 289363805342766598537338389 13563928375442184306437737)
    ·
      refine ⟨10172946281581638229828303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13563928375442184306437737 10172946281581638229828303)
      ·
        refine ⟨15259419422372457344742455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10172946281581638229828303 15259419422372457344742455)
        ·
          refine ⟨22889129133558686017113683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15259419422372457344742455 22889129133558686017113683)
          ·
            refine ⟨34333693700338029025670525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22889129133558686017113683 34333693700338029025670525)
            ·
              refine ⟨12875135137626760884626447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34333693700338029025670525 12875135137626760884626447)
              ·
                refine ⟨19312702706440141326939671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12875135137626760884626447 19312702706440141326939671)
                ·
                  refine ⟨28969054059660211990409507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19312702706440141326939671 28969054059660211990409507)
                  ·
                    refine ⟨43453581089490317985614261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28969054059660211990409507 43453581089490317985614261)
                    ·
                      refine ⟨4073773227139717311151337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43453581089490317985614261 4073773227139717311151337)
                      ·
                        rfl

theorem cell23_7933645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_7933645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933645 prefixEnd_7933645 := by exact prefixLift 7933645
  have htrace : WordTrace (prefixWord ++ tailWord_7933645) baseStart_7933645 baseEnd_7933645 := by
    simpa [prefixWord, tailWord_7933645, baseEnd_7933645] using wordTrace_append hprefix tailTrace_7933645
  have hstable : (prefixWord ++ tailWord_7933645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933645).length < 2 ^ (prefixWord ++ tailWord_7933645).sum := by decide
  have hdescent : baseEnd_7933645 < baseStart_7933645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933651 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 4, 7, 2]
def baseStart_7933651 : Nat := 118140960795 + 7933651 * 2 ^ 59
def prefixEnd_7933651 : Nat := 4983230072969 + 3 ^ 40 * 7933651 * 2
def baseEnd_7933651 : Nat := 4073776308023644287676309

theorem tailTrace_7933651 : CollatzResearch.WordTrace tailWord_7933651 prefixEnd_7933651 4073776308023644287676309 := by
  unfold tailWord_7933651
  simp only [CollatzResearch.WordTrace]
  refine ⟨289364024180744861562056807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192909349453829907708037871 289364024180744861562056807)
  ·
    refine ⟨434046036271117292343085211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289364024180744861562056807 434046036271117292343085211)
    ·
      refine ⟨651069054406675938514627817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434046036271117292343085211 651069054406675938514627817)
      ·
        refine ⟨488301790805006953885970863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 651069054406675938514627817 488301790805006953885970863)
        ·
          refine ⟨732452686207510430828956295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488301790805006953885970863 732452686207510430828956295)
          ·
            refine ⟨1098679029311265646243434443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732452686207510430828956295 1098679029311265646243434443)
            ·
              refine ⟨1648018543966898469365151665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098679029311265646243434443 1648018543966898469365151665)
              ·
                refine ⟨1236013907975173852023863749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1648018543966898469365151665 1236013907975173852023863749)
                ·
                  refine ⟨231752607745345097254474453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1236013907975173852023863749 231752607745345097254474453)
                  ·
                    refine ⟨5431701744031525716901745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 231752607745345097254474453 5431701744031525716901745)
                    ·
                      refine ⟨4073776308023644287676309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5431701744031525716901745 4073776308023644287676309)
                      ·
                        rfl

theorem cell23_7933651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 7, 2].length) (baseStart_7933651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933651 prefixEnd_7933651 := by exact prefixLift 7933651
  have htrace : WordTrace (prefixWord ++ tailWord_7933651) baseStart_7933651 baseEnd_7933651 := by
    simpa [prefixWord, tailWord_7933651, baseEnd_7933651] using wordTrace_append hprefix tailTrace_7933651
  have hstable : (prefixWord ++ tailWord_7933651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933651).length < 2 ^ (prefixWord ++ tailWord_7933651).sum := by decide
  have hdescent : baseEnd_7933651 < baseStart_7933651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933668 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 5, 3, 2]
def baseStart_7933668 : Nat := 118140960795 + 7933668 * 2 ^ 59
def prefixEnd_7933668 : Nat := 4983230072969 + 3 ^ 40 * 7933668 * 2
def baseEnd_7933668 : Nat := 4073785037194770721163731

theorem tailTrace_7933668 : CollatzResearch.WordTrace tailWord_7933668 prefixEnd_7933668 4073785037194770721163731 := by
  unfold tailWord_7933668
  simp only [CollatzResearch.WordTrace]
  refine ⟨144682322110841636732712829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192909762814455515643617105 144682322110841636732712829)
  ·
    refine ⟨54255870791565613774767311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144682322110841636732712829 54255870791565613774767311)
    ·
      refine ⟨81383806187348420662150967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54255870791565613774767311 81383806187348420662150967)
      ·
        refine ⟨122075709281022630993226451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81383806187348420662150967 122075709281022630993226451)
        ·
          refine ⟨183113563921533946489839677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122075709281022630993226451 183113563921533946489839677)
          ·
            refine ⟨68667586470575229933689879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183113563921533946489839677 68667586470575229933689879)
            ·
              refine ⟨103001379705862844900534819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68667586470575229933689879 103001379705862844900534819)
              ·
                refine ⟨154502069558794267350802229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103001379705862844900534819 154502069558794267350802229)
                ·
                  refine ⟨14484569021136962564137709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154502069558794267350802229 14484569021136962564137709)
                  ·
                    refine ⟨5431713382926360961551641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14484569021136962564137709 5431713382926360961551641)
                    ·
                      refine ⟨4073785037194770721163731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5431713382926360961551641 4073785037194770721163731)
                      ·
                        rfl

theorem cell23_7933668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_7933668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933668 prefixEnd_7933668 := by exact prefixLift 7933668
  have htrace : WordTrace (prefixWord ++ tailWord_7933668) baseStart_7933668 baseEnd_7933668 := by
    simpa [prefixWord, tailWord_7933668, baseEnd_7933668] using wordTrace_append hprefix tailTrace_7933668
  have hstable : (prefixWord ++ tailWord_7933668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933668).length < 2 ^ (prefixWord ++ tailWord_7933668).sum := by decide
  have hdescent : baseEnd_7933668 < baseStart_7933668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933715 : List Nat := [1, 1, 1, 2, 1, 3, 2, 6, 2, 2, 2]
def baseStart_7933715 : Nat := 118140960795 + 7933715 * 2 ^ 59
def prefixEnd_7933715 : Nat := 4983230072969 + 3 ^ 40 * 7933715 * 2
def baseEnd_7933715 : Nat := 4073809170785532037276015

theorem tailTrace_7933715 : CollatzResearch.WordTrace tailWord_7933715 prefixEnd_7933715 4073809170785532037276015 := by
  unfold tailWord_7933715
  simp only [CollatzResearch.WordTrace]
  refine ⟨289366358452513000492386599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192910905635008666994924399 289366358452513000492386599)
  ·
    refine ⟨434049537678769500738579899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289366358452513000492386599 434049537678769500738579899)
    ·
      refine ⟨651074306518154251107869849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434049537678769500738579899 651074306518154251107869849)
      ·
        refine ⟨488305729888615688330902387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 651074306518154251107869849 488305729888615688330902387)
        ·
          refine ⟨732458594832923532496353581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488305729888615688330902387 732458594832923532496353581)
          ·
            refine ⟨274671973062346324686132593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 732458594832923532496353581 274671973062346324686132593)
            ·
              refine ⟨206003979796759743514599445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274671973062346324686132593 206003979796759743514599445)
              ·
                refine ⟨9656436552973112977246849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 206003979796759743514599445 9656436552973112977246849)
                ·
                  refine ⟨7242327414729834732935137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9656436552973112977246849 7242327414729834732935137)
                  ·
                    refine ⟨5431745561047376049701353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7242327414729834732935137 5431745561047376049701353)
                    ·
                      refine ⟨4073809170785532037276015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5431745561047376049701353 4073809170785532037276015)
                      ·
                        rfl

theorem cell23_7933715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 2, 2].length) (baseStart_7933715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933715 prefixEnd_7933715 := by exact prefixLift 7933715
  have htrace : WordTrace (prefixWord ++ tailWord_7933715) baseStart_7933715 baseEnd_7933715 := by
    simpa [prefixWord, tailWord_7933715, baseEnd_7933715] using wordTrace_append hprefix tailTrace_7933715
  have hstable : (prefixWord ++ tailWord_7933715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933715).length < 2 ^ (prefixWord ++ tailWord_7933715).sum := by decide
  have hdescent : baseEnd_7933715 < baseStart_7933715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933726 : List Nat := [4, 3, 2, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_7933726 : Nat := 118140960795 + 7933726 * 2 ^ 59
def prefixEnd_7933726 : Nat := 4983230072969 + 3 ^ 40 * 7933726 * 2
def baseEnd_7933726 : Nat := 4073814819072731494238465

theorem tailTrace_7933726 : CollatzResearch.WordTrace tailWord_7933726 prefixEnd_7933726 4073814819072731494238465 := by
  unfold tailWord_7933726
  simp only [CollatzResearch.WordTrace]
  refine ⟨36170844956934143671379629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192911173103648766247358021 36170844956934143671379629)
  ·
    refine ⟨13564066858850303876767361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36170844956934143671379629 13564066858850303876767361)
    ·
      refine ⟨10173050144137727907575521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13564066858850303876767361 10173050144137727907575521)
      ·
        refine ⟨7629787608103295930681641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10173050144137727907575521 7629787608103295930681641)
        ·
          refine ⟨5722340706077471948011231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7629787608103295930681641 5722340706077471948011231)
          ·
            refine ⟨8583511059116207922016847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5722340706077471948011231 8583511059116207922016847)
            ·
              refine ⟨12875266588674311883025271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8583511059116207922016847 12875266588674311883025271)
              ·
                refine ⟨19312899883011467824537907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12875266588674311883025271 19312899883011467824537907)
                ·
                  refine ⟨28969349824517201736806861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19312899883011467824537907 28969349824517201736806861)
                  ·
                    refine ⟨10863506184193950651302573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28969349824517201736806861 10863506184193950651302573)
                    ·
                      refine ⟨4073814819072731494238465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10863506184193950651302573 4073814819072731494238465)
                      ·
                        rfl

theorem cell23_7933726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_7933726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933726 prefixEnd_7933726 := by exact prefixLift 7933726
  have htrace : WordTrace (prefixWord ++ tailWord_7933726) baseStart_7933726 baseEnd_7933726 := by
    simpa [prefixWord, tailWord_7933726, baseEnd_7933726] using wordTrace_append hprefix tailTrace_7933726
  have hstable : (prefixWord ++ tailWord_7933726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933726).length < 2 ^ (prefixWord ++ tailWord_7933726).sum := by decide
  have hdescent : baseEnd_7933726 < baseStart_7933726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933732 : List Nat := [2, 3, 1, 3, 2, 3, 1, 1, 1, 4, 2]
def baseStart_7933732 : Nat := 118140960795 + 7933732 * 2 ^ 59
def prefixEnd_7933732 : Nat := 4983230072969 + 3 ^ 40 * 7933732 * 2
def baseEnd_7933732 : Nat := 4073817899956658470763437

theorem tailTrace_7933732 : CollatzResearch.WordTrace tailWord_7933732 prefixEnd_7933732 4073817899956658470763437 := by
  unfold tailWord_7933732
  simp only [CollatzResearch.WordTrace]
  refine ⟨144683489246725706197877725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192911318995634274930503633 144683489246725706197877725)
  ·
    refine ⟨54256308467522139824204147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144683489246725706197877725 54256308467522139824204147)
    ·
      refine ⟨81384462701283209736306221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54256308467522139824204147 81384462701283209736306221)
      ·
        refine ⟨30519173512981203651114833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81384462701283209736306221 30519173512981203651114833)
        ·
          refine ⟨22889380134735902738336125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30519173512981203651114833 22889380134735902738336125)
          ·
            refine ⟨8583517550525963526876047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22889380134735902738336125 8583517550525963526876047)
            ·
              refine ⟨12875276325788945290314071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8583517550525963526876047 12875276325788945290314071)
              ·
                refine ⟨19312914488683417935471107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12875276325788945290314071 19312914488683417935471107)
                ·
                  refine ⟨28969371733025126903206661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19312914488683417935471107 28969371733025126903206661)
                  ·
                    refine ⟨5431757199942211294351249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28969371733025126903206661 5431757199942211294351249)
                    ·
                      refine ⟨4073817899956658470763437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5431757199942211294351249 4073817899956658470763437)
                      ·
                        rfl

theorem cell23_7933732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_7933732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933732 prefixEnd_7933732 := by exact prefixLift 7933732
  have htrace : WordTrace (prefixWord ++ tailWord_7933732) baseStart_7933732 baseEnd_7933732 := by
    simpa [prefixWord, tailWord_7933732, baseEnd_7933732] using wordTrace_append hprefix tailTrace_7933732
  have hstable : (prefixWord ++ tailWord_7933732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933732).length < 2 ^ (prefixWord ++ tailWord_7933732).sum := by decide
  have hdescent : baseEnd_7933732 < baseStart_7933732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933768 : List Nat := [2, 1, 3, 1, 1, 5, 1, 2, 2, 5]
def baseStart_7933768 : Nat := 118140960795 + 7933768 * 2 ^ 59
def prefixEnd_7933768 : Nat := 4983230072969 + 3 ^ 40 * 7933768 * 2
def baseEnd_7933768 : Nat := 1357945461753406776637757

theorem tailTrace_7933768 : CollatzResearch.WordTrace tailWord_7933768 prefixEnd_7933768 1357945461753406776637757 := by
  unfold tailWord_7933768
  simp only [CollatzResearch.WordTrace]
  refine ⟨144684145760660495272032979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192912194347547327029377305 144684145760660495272032979)
  ·
    refine ⟨217026218640990742908049469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144684145760660495272032979 217026218640990742908049469)
    ·
      refine ⟨81384831990371528590518551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217026218640990742908049469 81384831990371528590518551)
      ·
        refine ⟨122077247985557292885777827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81384831990371528590518551 122077247985557292885777827)
        ·
          refine ⟨183115871978335939328666741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122077247985557292885777827 183115871978335939328666741)
          ·
            refine ⟨17167112997968994312062507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183115871978335939328666741 17167112997968994312062507)
            ·
              refine ⟨25750669496953491468093761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17167112997968994312062507 25750669496953491468093761)
              ·
                refine ⟨19313002122715118601070321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25750669496953491468093761 19313002122715118601070321)
                ·
                  refine ⟨14484751592036338950802741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19313002122715118601070321 14484751592036338950802741)
                  ·
                    refine ⟨1357945461753406776637757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14484751592036338950802741 1357945461753406776637757)
                    ·
                      rfl

theorem cell23_7933768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_7933768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933768 prefixEnd_7933768 := by exact prefixLift 7933768
  have htrace : WordTrace (prefixWord ++ tailWord_7933768) baseStart_7933768 baseEnd_7933768 := by
    simpa [prefixWord, tailWord_7933768, baseEnd_7933768] using wordTrace_append hprefix tailTrace_7933768
  have hstable : (prefixWord ++ tailWord_7933768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933768).length < 2 ^ (prefixWord ++ tailWord_7933768).sum := by decide
  have hdescent : baseEnd_7933768 < baseStart_7933768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933772 : List Nat := [2, 2, 1, 3, 4, 1, 3, 2, 5]
def baseStart_7933772 : Nat := 118140960795 + 7933772 * 2 ^ 59
def prefixEnd_7933772 : Nat := 4983230072969 + 3 ^ 40 * 7933772 * 2
def baseEnd_7933772 : Nat := 452648715464759812695917

theorem tailTrace_7933772 : CollatzResearch.WordTrace tailWord_7933772 prefixEnd_7933772 452648715464759812695917 := by
  unfold tailWord_7933772
  simp only [CollatzResearch.WordTrace]
  refine ⟨144684218706653249613605785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192912291608870999484807713 144684218706653249613605785)
  ·
    refine ⟨108513164029989937210204339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144684218706653249613605785 108513164029989937210204339)
    ·
      refine ⟨162769746044984905815306509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108513164029989937210204339 162769746044984905815306509)
      ·
        refine ⟨61038654766869339680739941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162769746044984905815306509 61038654766869339680739941)
        ·
          refine ⟨11444747768788001190138739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61038654766869339680739941 11444747768788001190138739)
          ·
            refine ⟨17167121653182001785208109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11444747768788001190138739 17167121653182001785208109)
            ·
              refine ⟨6437670619943250669453041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17167121653182001785208109 6437670619943250669453041)
              ·
                refine ⟨4828252964957438002089781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6437670619943250669453041 4828252964957438002089781)
                ·
                  refine ⟨452648715464759812695917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4828252964957438002089781 452648715464759812695917)
                  ·
                    rfl

theorem cell23_7933772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 5].length) (baseStart_7933772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933772 prefixEnd_7933772 := by exact prefixLift 7933772
  have htrace : WordTrace (prefixWord ++ tailWord_7933772) baseStart_7933772 baseEnd_7933772 := by
    simpa [prefixWord, tailWord_7933772, baseEnd_7933772] using wordTrace_append hprefix tailTrace_7933772
  have hstable : (prefixWord ++ tailWord_7933772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933772).length < 2 ^ (prefixWord ++ tailWord_7933772).sum := by decide
  have hdescent : baseEnd_7933772 < baseStart_7933772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933778 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_7933778 : Nat := 118140960795 + 7933778 * 2 ^ 59
def prefixEnd_7933778 : Nat := 4983230072969 + 3 ^ 40 * 7933778 * 2
def baseEnd_7933778 : Nat := 4073841520066765290788225

theorem tailTrace_7933778 : CollatzResearch.WordTrace tailWord_7933778 prefixEnd_7933778 4073841520066765290788225 := by
  unfold tailWord_7933778
  simp only [CollatzResearch.WordTrace]
  refine ⟨72342164062821190562982497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192912437500856508167953325 72342164062821190562982497)
  ·
    refine ⟨54256623047115892922236873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72342164062821190562982497 54256623047115892922236873)
    ·
      refine ⟨40692467285336919691677655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54256623047115892922236873 40692467285336919691677655)
      ·
        refine ⟨61038700928005379537516483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40692467285336919691677655 61038700928005379537516483)
        ·
          refine ⟨91558051392008069306274725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61038700928005379537516483 91558051392008069306274725)
          ·
            refine ⟨17167134636001512994926511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91558051392008069306274725 17167134636001512994926511)
            ·
              refine ⟨25750701954002269492389767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17167134636001512994926511 25750701954002269492389767)
              ·
                refine ⟨38626052931003404238584651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25750701954002269492389767 38626052931003404238584651)
                ·
                  refine ⟨57939079396505106357876977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38626052931003404238584651 57939079396505106357876977)
                  ·
                    refine ⟨43454309547378829768407733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57939079396505106357876977 43454309547378829768407733)
                    ·
                      refine ⟨4073841520066765290788225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43454309547378829768407733 4073841520066765290788225)
                      ·
                        rfl

theorem cell23_7933778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_7933778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933778 prefixEnd_7933778 := by exact prefixLift 7933778
  have htrace : WordTrace (prefixWord ++ tailWord_7933778) baseStart_7933778 baseEnd_7933778 := by
    simpa [prefixWord, tailWord_7933778, baseEnd_7933778] using wordTrace_append hprefix tailTrace_7933778
  have hstable : (prefixWord ++ tailWord_7933778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933778).length < 2 ^ (prefixWord ++ tailWord_7933778).sum := by decide
  have hdescent : baseEnd_7933778 < baseStart_7933778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933801 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 2, 4, 4]
def baseStart_7933801 : Nat := 118140960795 + 7933801 * 2 ^ 59
def prefixEnd_7933801 : Nat := 4983230072969 + 3 ^ 40 * 7933801 * 2
def baseEnd_7933801 : Nat := 4073853330121818700800619

theorem tailTrace_7933801 : CollatzResearch.WordTrace tailWord_7933801 prefixEnd_7933801 4073853330121818700800619 := by
  unfold tailWord_7933801
  simp only [CollatzResearch.WordTrace]
  refine ⟨289369495130201437180017257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192912996753467624786678171 289369495130201437180017257)
  ·
    refine ⟨217027121347651077885012943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289369495130201437180017257 217027121347651077885012943)
    ·
      refine ⟨325540682021476616827519415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217027121347651077885012943 325540682021476616827519415)
      ·
        refine ⟨488311023032214925241279123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325540682021476616827519415 488311023032214925241279123)
        ·
          refine ⟨732466534548322387861918685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488311023032214925241279123 732466534548322387861918685)
          ·
            refine ⟨274674950455620895448219507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 732466534548322387861918685 274674950455620895448219507)
            ·
              refine ⟨412012425683431343172329261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274674950455620895448219507 412012425683431343172329261)
              ·
                refine ⟨154504659631286753689623473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 412012425683431343172329261 154504659631286753689623473)
                ·
                  refine ⟨115878494723465065267217605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154504659631286753689623473 115878494723465065267217605)
                  ·
                    refine ⟨21727217760649699737603301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115878494723465065267217605 21727217760649699737603301)
                    ·
                      refine ⟨4073853330121818700800619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21727217760649699737603301 4073853330121818700800619)
                      ·
                        rfl

theorem cell23_7933801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_7933801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933801 prefixEnd_7933801 := by exact prefixLift 7933801
  have htrace : WordTrace (prefixWord ++ tailWord_7933801) baseStart_7933801 baseEnd_7933801 := by
    simpa [prefixWord, tailWord_7933801, baseEnd_7933801] using wordTrace_append hprefix tailTrace_7933801
  have hstable : (prefixWord ++ tailWord_7933801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933801).length < 2 ^ (prefixWord ++ tailWord_7933801).sum := by decide
  have hdescent : baseEnd_7933801 < baseStart_7933801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933802 : List Nat := [3, 1, 3, 4, 1, 1, 2, 1, 2, 5]
def baseStart_7933802 : Nat := 118140960795 + 7933802 * 2 ^ 59
def prefixEnd_7933802 : Nat := 4983230072969 + 3 ^ 40 * 7933802 * 2
def baseEnd_7933802 : Nat := 1357951281200824398962705

theorem tailTrace_7933802 : CollatzResearch.WordTrace tailWord_7933802 prefixEnd_7933802 1357951281200824398962705 := by
  unfold tailWord_7933802
  simp only [CollatzResearch.WordTrace]
  refine ⟨72342382900799453587700915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192913021068798542900535773 72342382900799453587700915)
  ·
    refine ⟨108513574351199180381551373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72342382900799453587700915 108513574351199180381551373)
    ·
      refine ⟨40692590381699692643081765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108513574351199180381551373 40692590381699692643081765)
      ·
        refine ⟨7629860696568692370577831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40692590381699692643081765 7629860696568692370577831)
        ·
          refine ⟨11444791044853038555866747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7629860696568692370577831 11444791044853038555866747)
          ·
            refine ⟨17167186567279557833800121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11444791044853038555866747 17167186567279557833800121)
            ·
              refine ⟨12875389925459668375350091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17167186567279557833800121 12875389925459668375350091)
              ·
                refine ⟨19313084888189502563025137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12875389925459668375350091 19313084888189502563025137)
                ·
                  refine ⟨14484813666142126922268853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19313084888189502563025137 14484813666142126922268853)
                  ·
                    refine ⟨1357951281200824398962705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14484813666142126922268853 1357951281200824398962705)
                    ·
                      rfl

theorem cell23_7933802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_7933802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933802 prefixEnd_7933802 := by exact prefixLift 7933802
  have htrace : WordTrace (prefixWord ++ tailWord_7933802) baseStart_7933802 baseEnd_7933802 := by
    simpa [prefixWord, tailWord_7933802, baseEnd_7933802] using wordTrace_append hprefix tailTrace_7933802
  have hstable : (prefixWord ++ tailWord_7933802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933802).length < 2 ^ (prefixWord ++ tailWord_7933802).sum := by decide
  have hdescent : baseEnd_7933802 < baseStart_7933802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933822 : List Nat := [4, 2, 3, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_7933822 : Nat := 118140960795 + 7933822 * 2 ^ 59
def prefixEnd_7933822 : Nat := 4983230072969 + 3 ^ 40 * 7933822 * 2
def baseEnd_7933822 : Nat := 4073864113215563118638023

theorem tailTrace_7933822 : CollatzResearch.WordTrace tailWord_7933822 prefixEnd_7933822 4073864113215563118638023 := by
  unfold tailWord_7933822
  simp only [CollatzResearch.WordTrace]
  refine ⟨36171282632890669720816465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192913507375416905177687813 36171282632890669720816465)
  ·
    refine ⟨27128461974668002290612349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36171282632890669720816465 27128461974668002290612349)
    ·
      refine ⟨10173173240500500858979631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27128461974668002290612349 10173173240500500858979631)
      ·
        refine ⟨15259759860750751288469447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10173173240500500858979631 15259759860750751288469447)
        ·
          refine ⟨22889639791126126932704171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15259759860750751288469447 22889639791126126932704171)
          ·
            refine ⟨34334459686689190399056257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22889639791126126932704171 34334459686689190399056257)
            ·
              refine ⟨25750844765016892799292193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34334459686689190399056257 25750844765016892799292193)
              ·
                refine ⟨19313133573762669599469145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25750844765016892799292193 19313133573762669599469145)
                ·
                  refine ⟨14484850180322002199601859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19313133573762669599469145 14484850180322002199601859)
                  ·
                    refine ⟨21727275270483003299402789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14484850180322002199601859 21727275270483003299402789)
                    ·
                      refine ⟨4073864113215563118638023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21727275270483003299402789 4073864113215563118638023)
                      ·
                        rfl

theorem cell23_7933822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_7933822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933822 prefixEnd_7933822 := by exact prefixLift 7933822
  have htrace : WordTrace (prefixWord ++ tailWord_7933822) baseStart_7933822 baseEnd_7933822 := by
    simpa [prefixWord, tailWord_7933822, baseEnd_7933822] using wordTrace_append hprefix tailTrace_7933822
  have hstable : (prefixWord ++ tailWord_7933822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933822).length < 2 ^ (prefixWord ++ tailWord_7933822).sum := by decide
  have hdescent : baseEnd_7933822 < baseStart_7933822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933828 : List Nat := [2, 3, 2, 1, 1, 1, 3, 4, 6]
def baseStart_7933828 : Nat := 118140960795 + 7933828 * 2 ^ 59
def prefixEnd_7933828 : Nat := 4983230072969 + 3 ^ 40 * 7933828 * 2
def baseEnd_7933828 : Nat := 452651910455498899462555

theorem tailTrace_7933828 : CollatzResearch.WordTrace tailWord_7933828 prefixEnd_7933828 452651910455498899462555 := by
  unfold tailWord_7933828
  simp only [CollatzResearch.WordTrace]
  refine ⟨144685239950551810395625069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192913653267402413860833425 144685239950551810395625069)
  ·
    refine ⟨54256964981456928898359401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144685239950551810395625069 54256964981456928898359401)
    ·
      refine ⟨40692723736092696673769551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54256964981456928898359401 40692723736092696673769551)
      ·
        refine ⟨61039085604139045010654327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40692723736092696673769551 61039085604139045010654327)
        ·
          refine ⟨91558628406208567515981491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61039085604139045010654327 91558628406208567515981491)
          ·
            refine ⟨137337942609312851273972237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91558628406208567515981491 137337942609312851273972237)
            ·
              refine ⟨51501728478492319227739589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137337942609312851273972237 51501728478492319227739589)
              ·
                refine ⟨9656574089717309855201173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51501728478492319227739589 9656574089717309855201173)
                ·
                  refine ⟨452651910455498899462555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9656574089717309855201173 452651910455498899462555)
                  ·
                    rfl

theorem cell23_7933828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_7933828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933828 prefixEnd_7933828 := by exact prefixLift 7933828
  have htrace : WordTrace (prefixWord ++ tailWord_7933828) baseStart_7933828 baseEnd_7933828 := by
    simpa [prefixWord, tailWord_7933828, baseEnd_7933828] using wordTrace_append hprefix tailTrace_7933828
  have hstable : (prefixWord ++ tailWord_7933828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933828).length < 2 ^ (prefixWord ++ tailWord_7933828).sum := by decide
  have hdescent : baseEnd_7933828 < baseStart_7933828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933865 : List Nat := [1, 2, 1, 1, 1, 1, 4, 5, 2, 3, 2]
def baseStart_7933865 : Nat := 118140960795 + 7933865 * 2 ^ 59
def prefixEnd_7933865 : Nat := 4983230072969 + 3 ^ 40 * 7933865 * 2
def baseEnd_7933865 : Nat := 4073886192883706450400325

theorem tailTrace_7933865 : CollatzResearch.WordTrace tailWord_7933865 prefixEnd_7933865 4073886192883706450400325 := by
  unfold tailWord_7933865
  simp only [CollatzResearch.WordTrace]
  refine ⟨289371829401969576110347049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192914552934646384073564699 289371829401969576110347049)
  ·
    refine ⟨217028872051477182082760287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289371829401969576110347049 217028872051477182082760287)
    ·
      refine ⟨325543308077215773124140431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217028872051477182082760287 325543308077215773124140431)
      ·
        refine ⟨488314962115823659686210647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325543308077215773124140431 488314962115823659686210647)
        ·
          refine ⟨732472443173735489529315971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488314962115823659686210647 732472443173735489529315971)
          ·
            refine ⟨1098708664760603234293973957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732472443173735489529315971 1098708664760603234293973957)
            ·
              refine ⟨206007874642613106430120117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1098708664760603234293973957 206007874642613106430120117)
              ·
                refine ⟨19313238247744978727823761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 206007874642613106430120117 19313238247744978727823761)
                ·
                  refine ⟨14484928685808734045867821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19313238247744978727823761 14484928685808734045867821)
                  ·
                    refine ⟨5431848257178275267200433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14484928685808734045867821 5431848257178275267200433)
                    ·
                      refine ⟨4073886192883706450400325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5431848257178275267200433 4073886192883706450400325)
                      ·
                        rfl

theorem cell23_7933865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 3, 2].length) (baseStart_7933865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933865 prefixEnd_7933865 := by exact prefixLift 7933865
  have htrace : WordTrace (prefixWord ++ tailWord_7933865) baseStart_7933865 baseEnd_7933865 := by
    simpa [prefixWord, tailWord_7933865, baseEnd_7933865] using wordTrace_append hprefix tailTrace_7933865
  have hstable : (prefixWord ++ tailWord_7933865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933865).length < 2 ^ (prefixWord ++ tailWord_7933865).sum := by decide
  have hdescent : baseEnd_7933865 < baseStart_7933865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933898 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_7933898 : Nat := 118140960795 + 7933898 * 2 ^ 59
def prefixEnd_7933898 : Nat := 4983230072969 + 3 ^ 40 * 7933898 * 2
def baseEnd_7933898 : Nat := 4073903137745304821287673

theorem tailTrace_7933898 : CollatzResearch.WordTrace tailWord_7933898 prefixEnd_7933898 4073903137745304821287673 := by
  unfold tailWord_7933898
  simp only [CollatzResearch.WordTrace]
  refine ⟨72343258252712505686574587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192915355340566681830865565 72343258252712505686574587)
  ·
    refine ⟨108514887379068758529861881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72343258252712505686574587 108514887379068758529861881)
    ·
      refine ⟨81386165534301568897396411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108514887379068758529861881 81386165534301568897396411)
      ·
        refine ⟨122079248301452353346094617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81386165534301568897396411 122079248301452353346094617)
        ·
          refine ⟨91559436226089265009570963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122079248301452353346094617 91559436226089265009570963)
          ·
            refine ⟨137339154339133897514356445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91559436226089265009570963 137339154339133897514356445)
            ·
              refine ⟨51502182877175211567883667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137339154339133897514356445 51502182877175211567883667)
              ·
                refine ⟨77253274315762817351825501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51502182877175211567883667 77253274315762817351825501)
                ·
                  refine ⟨28969977868411056506934563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77253274315762817351825501 28969977868411056506934563)
                  ·
                    refine ⟨43454966802616584760401845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28969977868411056506934563 43454966802616584760401845)
                    ·
                      refine ⟨4073903137745304821287673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43454966802616584760401845 4073903137745304821287673)
                      ·
                        rfl

theorem cell23_7933898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_7933898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933898 prefixEnd_7933898 := by exact prefixLift 7933898
  have htrace : WordTrace (prefixWord ++ tailWord_7933898) baseStart_7933898 baseEnd_7933898 := by
    simpa [prefixWord, tailWord_7933898, baseEnd_7933898] using wordTrace_append hprefix tailTrace_7933898
  have hstable : (prefixWord ++ tailWord_7933898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933898).length < 2 ^ (prefixWord ++ tailWord_7933898).sum := by decide
  have hdescent : baseEnd_7933898 < baseStart_7933898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933912 : List Nat := [2, 1, 2, 2, 2, 2, 1, 4, 3, 2, 2]
def baseStart_7933912 : Nat := 118140960795 + 7933912 * 2 ^ 59
def prefixEnd_7933912 : Nat := 4983230072969 + 3 ^ 40 * 7933912 * 2
def baseEnd_7933912 : Nat := 4073910326474467766512609

theorem tailTrace_7933912 : CollatzResearch.WordTrace tailWord_7933912 prefixEnd_7933912 4073910326474467766512609 := by
  unfold tailWord_7933912
  simp only [CollatzResearch.WordTrace]
  refine ⟨144686771816399651568653995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192915695755199535424871993 144686771816399651568653995)
  ·
    refine ⟨217030157724599477352980993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144686771816399651568653995 217030157724599477352980993)
    ·
      refine ⟨162772618293449608014735745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217030157724599477352980993 162772618293449608014735745)
      ·
        refine ⟨122079463720087206011051809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162772618293449608014735745 122079463720087206011051809)
        ·
          refine ⟨91559597790065404508288857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122079463720087206011051809 91559597790065404508288857)
          ·
            refine ⟨68669698342549053381216643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91559597790065404508288857 68669698342549053381216643)
            ·
              refine ⟨103004547513823580071824965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68669698342549053381216643 103004547513823580071824965)
              ·
                refine ⟨19313352658841921263467181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103004547513823580071824965 19313352658841921263467181)
                ·
                  refine ⟨7242507247065720473800193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19313352658841921263467181 7242507247065720473800193)
                  ·
                    refine ⟨5431880435299290355350145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7242507247065720473800193 5431880435299290355350145)
                    ·
                      refine ⟨4073910326474467766512609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5431880435299290355350145 4073910326474467766512609)
                      ·
                        rfl

theorem cell23_7933912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_7933912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933912 prefixEnd_7933912 := by exact prefixLift 7933912
  have htrace : WordTrace (prefixWord ++ tailWord_7933912) baseStart_7933912 baseEnd_7933912 := by
    simpa [prefixWord, tailWord_7933912, baseEnd_7933912] using wordTrace_append hprefix tailTrace_7933912
  have hstable : (prefixWord ++ tailWord_7933912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933912).length < 2 ^ (prefixWord ++ tailWord_7933912).sum := by decide
  have hdescent : baseEnd_7933912 < baseStart_7933912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933948 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 2, 7]
def baseStart_7933948 : Nat := 118140960795 + 7933948 * 2 ^ 59
def prefixEnd_7933948 : Nat := 4983230072969 + 3 ^ 40 * 7933948 * 2
def baseEnd_7933948 : Nat := 1357976270592676541887481

theorem tailTrace_7933948 : CollatzResearch.WordTrace tailWord_7933948 prefixEnd_7933948 1357976270592676541887481 := by
  unfold tailWord_7933948
  simp only [CollatzResearch.WordTrace]
  refine ⟨144687428330334440642809249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192916571107112587523745665 144687428330334440642809249)
  ·
    refine ⟨108515571247750830482106937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144687428330334440642809249 108515571247750830482106937)
    ·
      refine ⟨81386678435813122861580203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108515571247750830482106937 81386678435813122861580203)
      ·
        refine ⟨122080017653719684292370305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81386678435813122861580203 122080017653719684292370305)
        ·
          refine ⟨91560013240289763219277729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122080017653719684292370305 91560013240289763219277729)
          ·
            refine ⟨68670009930217322414458297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91560013240289763219277729 68670009930217322414458297)
            ·
              refine ⟨51502507447662991810843723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68670009930217322414458297 51502507447662991810843723)
              ·
                refine ⟨77253761171494487716265585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51502507447662991810843723 77253761171494487716265585)
                ·
                  refine ⟨57940320878620865787199189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77253761171494487716265585 57940320878620865787199189)
                  ·
                    refine ⟨1357976270592676541887481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57940320878620865787199189 1357976270592676541887481)
                    ·
                      rfl

theorem cell23_7933948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_7933948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933948 prefixEnd_7933948 := by exact prefixLift 7933948
  have htrace : WordTrace (prefixWord ++ tailWord_7933948) baseStart_7933948 baseEnd_7933948 := by
    simpa [prefixWord, tailWord_7933948, baseEnd_7933948] using wordTrace_append hprefix tailTrace_7933948
  have hstable : (prefixWord ++ tailWord_7933948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933948).length < 2 ^ (prefixWord ++ tailWord_7933948).sum := by decide
  have hdescent : baseEnd_7933948 < baseStart_7933948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7933968 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 4]
def baseStart_7933968 : Nat := 118140960795 + 7933968 * 2 ^ 59
def prefixEnd_7933968 : Nat := 4983230072969 + 3 ^ 40 * 7933968 * 2
def baseEnd_7933968 : Nat := 4073939081391119547412351

theorem tailTrace_7933968 : CollatzResearch.WordTrace tailWord_7933968 prefixEnd_7933968 4073939081391119547412351 := by
  unfold tailWord_7933968
  simp only [CollatzResearch.WordTrace]
  refine ⟨144687793060298212350673279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192917057413730949800897705 144687793060298212350673279)
  ·
    refine ⟨217031689590447318526009919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144687793060298212350673279 217031689590447318526009919)
    ·
      refine ⟨325547534385670977789014879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217031689590447318526009919 325547534385670977789014879)
      ·
        refine ⟨488321301578506466683522319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325547534385670977789014879 488321301578506466683522319)
        ·
          refine ⟨732481952367759700025283479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488321301578506466683522319 732481952367759700025283479)
          ·
            refine ⟨1098722928551639550037925219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732481952367759700025283479 1098722928551639550037925219)
            ·
              refine ⟨1648084392827459325056887829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098722928551639550037925219 1648084392827459325056887829)
              ·
                refine ⟨77253955913787155862041617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1648084392827459325056887829 77253955913787155862041617)
                ·
                  refine ⟨57940466935340366896531213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77253955913787155862041617 57940466935340366896531213)
                  ·
                    refine ⟨21727675100752637586199205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57940466935340366896531213 21727675100752637586199205)
                    ·
                      refine ⟨4073939081391119547412351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21727675100752637586199205 4073939081391119547412351)
                      ·
                        rfl

theorem cell23_7933968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_7933968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7933968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7933968 prefixEnd_7933968 := by exact prefixLift 7933968
  have htrace : WordTrace (prefixWord ++ tailWord_7933968) baseStart_7933968 baseEnd_7933968 := by
    simpa [prefixWord, tailWord_7933968, baseEnd_7933968] using wordTrace_append hprefix tailTrace_7933968
  have hstable : (prefixWord ++ tailWord_7933968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7933968).length < 2 ^ (prefixWord ++ tailWord_7933968).sum := by decide
  have hdescent : baseEnd_7933968 < baseStart_7933968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7933968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934005 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_7934005 : Nat := 118140960795 + 7934005 * 2 ^ 59
def prefixEnd_7934005 : Nat := 4983230072969 + 3 ^ 40 * 7934005 * 2
def baseEnd_7934005 : Nat := 4073958080175335902649681

theorem tailTrace_7934005 : CollatzResearch.WordTrace tailWord_7934005 prefixEnd_7934005 4073958080175335902649681 := by
  unfold tailWord_7934005
  simp only [CollatzResearch.WordTrace]
  refine ⟨289376935621462380020443469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192917957080974920013628979 289376935621462380020443469)
  ·
    refine ⟨108516350858048392507666301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289376935621462380020443469 108516350858048392507666301)
    ·
      refine ⟨40693631571768147190374863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108516350858048392507666301 40693631571768147190374863)
      ·
        refine ⟨61040447357652220785562295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40693631571768147190374863 61040447357652220785562295)
        ·
          refine ⟨91560671036478331178343443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61040447357652220785562295 91560671036478331178343443)
          ·
            refine ⟨137341006554717496767515165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91560671036478331178343443 137341006554717496767515165)
            ·
              refine ⟨51502877458019061287818187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137341006554717496767515165 51502877458019061287818187)
              ·
                refine ⟨77254316187028591931727281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51502877458019061287818187 77254316187028591931727281)
                ·
                  refine ⟨57940737140271443948795461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77254316187028591931727281 57940737140271443948795461)
                  ·
                    refine ⟨10863888213800895740399149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57940737140271443948795461 10863888213800895740399149)
                    ·
                      refine ⟨4073958080175335902649681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10863888213800895740399149 4073958080175335902649681)
                      ·
                        rfl

theorem cell23_7934005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_7934005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934005 prefixEnd_7934005 := by exact prefixLift 7934005
  have htrace : WordTrace (prefixWord ++ tailWord_7934005) baseStart_7934005 baseEnd_7934005 := by
    simpa [prefixWord, tailWord_7934005, baseEnd_7934005] using wordTrace_append hprefix tailTrace_7934005
  have hstable : (prefixWord ++ tailWord_7934005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934005).length < 2 ^ (prefixWord ++ tailWord_7934005).sum := by decide
  have hdescent : baseEnd_7934005 < baseStart_7934005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934042 : List Nat := [3, 1, 1, 2, 1, 1, 6, 3, 5]
def baseStart_7934042 : Nat := 118140960795 + 7934042 * 2 ^ 59
def prefixEnd_7934042 : Nat := 4983230072969 + 3 ^ 40 * 7934042 * 2
def baseEnd_7934042 : Nat := 452664119884394695320779

theorem tailTrace_7934042 : CollatzResearch.WordTrace tailWord_7934042 prefixEnd_7934042 452664119884394695320779 := by
  unfold tailWord_7934042
  simp only [CollatzResearch.WordTrace]
  refine ⟨72344571280582083834885095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192918856748218890226360253 72344571280582083834885095)
  ·
    refine ⟨108516856920873125752327643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72344571280582083834885095 108516856920873125752327643)
    ·
      refine ⟨162775285381309688628491465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108516856920873125752327643 162775285381309688628491465)
      ·
        refine ⟨122081464035982266471368599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162775285381309688628491465 122081464035982266471368599)
        ·
          refine ⟨183122196053973399707052899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122081464035982266471368599 183122196053973399707052899)
          ·
            refine ⟨274683294080960099560579349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183122196053973399707052899 274683294080960099560579349)
            ·
              refine ⟨12875779410045004666902157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 274683294080960099560579349 12875779410045004666902157)
              ·
                refine ⟨4828417278766876750088309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12875779410045004666902157 4828417278766876750088309)
                ·
                  refine ⟨452664119884394695320779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4828417278766876750088309 452664119884394695320779)
                  ·
                    rfl

theorem cell23_7934042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 5].length) (baseStart_7934042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934042 prefixEnd_7934042 := by exact prefixLift 7934042
  have htrace : WordTrace (prefixWord ++ tailWord_7934042) baseStart_7934042 baseEnd_7934042 := by
    simpa [prefixWord, tailWord_7934042, baseEnd_7934042] using wordTrace_append hprefix tailTrace_7934042
  have hstable : (prefixWord ++ tailWord_7934042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934042).length < 2 ^ (prefixWord ++ tailWord_7934042).sum := by decide
  have hdescent : baseEnd_7934042 < baseStart_7934042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934055 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 4, 5]
def baseStart_7934055 : Nat := 118140960795 + 7934055 * 2 ^ 59
def prefixEnd_7934055 : Nat := 4983230072969 + 3 ^ 40 * 7934055 * 2
def baseEnd_7934055 : Nat := 1357994584736020235674817

theorem tailTrace_7934055 : CollatzResearch.WordTrace tailWord_7934055 prefixEnd_7934055 1357994584736020235674817 := by
  unfold tailWord_7934055
  simp only [CollatzResearch.WordTrace]
  refine ⟨289378759271281238559763619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192919172847520825706509079 289378759271281238559763619)
  ·
    refine ⟨434068138906921857839645429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289378759271281238559763619 434068138906921857839645429)
    ·
      refine ⟨40693888022523924172466759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 434068138906921857839645429 40693888022523924172466759)
      ·
        refine ⟨61040832033785886258700139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40693888022523924172466759 61040832033785886258700139)
        ·
          refine ⟨91561248050678829388050209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61040832033785886258700139 91561248050678829388050209)
          ·
            refine ⟨68670936038009122041037657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91561248050678829388050209 68670936038009122041037657)
            ·
              refine ⟨51503202028506841530778243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68670936038009122041037657 51503202028506841530778243)
              ·
                refine ⟨77254803042760262296167365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51503202028506841530778243 77254803042760262296167365)
                ·
                  refine ⟨14485275570517549180531381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77254803042760262296167365 14485275570517549180531381)
                  ·
                    refine ⟨1357994584736020235674817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14485275570517549180531381 1357994584736020235674817)
                    ·
                      rfl

theorem cell23_7934055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_7934055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934055 prefixEnd_7934055 := by exact prefixLift 7934055
  have htrace : WordTrace (prefixWord ++ tailWord_7934055) baseStart_7934055 baseEnd_7934055 := by
    simpa [prefixWord, tailWord_7934055, baseEnd_7934055] using wordTrace_append hprefix tailTrace_7934055
  have hstable : (prefixWord ++ tailWord_7934055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934055).length < 2 ^ (prefixWord ++ tailWord_7934055).sum := by decide
  have hdescent : baseEnd_7934055 < baseStart_7934055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934112 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 3]
def baseStart_7934112 : Nat := 118140960795 + 7934112 * 2 ^ 59
def prefixEnd_7934112 : Nat := 4983230072969 + 3 ^ 40 * 7934112 * 2
def baseEnd_7934112 : Nat := 4074013022605366984011689

theorem tailTrace_7934112 : CollatzResearch.WordTrace tailWord_7934112 prefixEnd_7934112 4074013022605366984011689 := by
  unfold tailWord_7934112
  simp only [CollatzResearch.WordTrace]
  refine ⟨144690419116037368647294295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192920558821383158196392393 144690419116037368647294295)
  ·
    refine ⟨217035628674056052970941443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144690419116037368647294295 217035628674056052970941443)
    ·
      refine ⟨325553443011084079456412165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217035628674056052970941443 325553443011084079456412165)
      ·
        refine ⟨61041270564578264898077281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325553443011084079456412165 61041270564578264898077281)
        ·
          refine ⟨45780952923433698673557961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61041270564578264898077281 45780952923433698673557961)
          ·
            refine ⟨34335714692575274005168471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45780952923433698673557961 34335714692575274005168471)
            ·
              refine ⟨51503572038862911007752707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34335714692575274005168471 51503572038862911007752707)
              ·
                refine ⟨77255358058294366511629061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51503572038862911007752707 77255358058294366511629061)
                ·
                  refine ⟨14485379635930193720930449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77255358058294366511629061 14485379635930193720930449)
                  ·
                    refine ⟨10864034726947645290697837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14485379635930193720930449 10864034726947645290697837)
                    ·
                      refine ⟨4074013022605366984011689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10864034726947645290697837 4074013022605366984011689)
                      ·
                        rfl

theorem cell23_7934112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_7934112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934112 prefixEnd_7934112 := by exact prefixLift 7934112
  have htrace : WordTrace (prefixWord ++ tailWord_7934112) baseStart_7934112 baseEnd_7934112 := by
    simpa [prefixWord, tailWord_7934112, baseEnd_7934112] using wordTrace_append hprefix tailTrace_7934112
  have hstable : (prefixWord ++ tailWord_7934112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934112).length < 2 ^ (prefixWord ++ tailWord_7934112).sum := by decide
  have hdescent : baseEnd_7934112 < baseStart_7934112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934166 : List Nat := [5, 2, 1, 2, 1, 2, 2, 2, 6]
def baseStart_7934166 : Nat := 118140960795 + 7934166 * 2 ^ 59
def prefixEnd_7934166 : Nat := 4983230072969 + 3 ^ 40 * 7934166 * 2
def baseEnd_7934166 : Nat := 452671194506745530304049

theorem tailTrace_7934166 : CollatzResearch.WordTrace tailWord_7934166 prefixEnd_7934166 452671194506745530304049 := by
  unfold tailWord_7934166
  simp only [CollatzResearch.WordTrace]
  refine ⟨18086425485867444032315897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192921871849252736344702901 18086425485867444032315897)
  ·
    refine ⟨13564819114400583024236923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18086425485867444032315897 13564819114400583024236923)
    ·
      refine ⟨20347228671600874536355385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13564819114400583024236923 20347228671600874536355385)
      ·
        refine ⟨15260421503700655902266539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20347228671600874536355385 15260421503700655902266539)
        ·
          refine ⟨22890632255550983853399809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15260421503700655902266539 22890632255550983853399809)
          ·
            refine ⟨17167974191663237890049857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22890632255550983853399809 17167974191663237890049857)
            ·
              refine ⟨12875980643747428417537393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17167974191663237890049857 12875980643747428417537393)
              ·
                refine ⟨9656985482810571313153045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12875980643747428417537393 9656985482810571313153045)
                ·
                  refine ⟨452671194506745530304049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9656985482810571313153045 452671194506745530304049)
                  ·
                    rfl

theorem cell23_7934166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_7934166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934166 prefixEnd_7934166 := by exact prefixLift 7934166
  have htrace : WordTrace (prefixWord ++ tailWord_7934166) baseStart_7934166 baseEnd_7934166 := by
    simpa [prefixWord, tailWord_7934166, baseEnd_7934166] using wordTrace_append hprefix tailTrace_7934166
  have hstable : (prefixWord ++ tailWord_7934166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934166).length < 2 ^ (prefixWord ++ tailWord_7934166).sum := by decide
  have hdescent : baseEnd_7934166 < baseStart_7934166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934169 : List Nat := [1, 2, 1, 2, 3, 1, 4, 2, 2, 3, 2]
def baseStart_7934169 : Nat := 118140960795 + 7934169 * 2 ^ 59
def prefixEnd_7934169 : Nat := 4983230072969 + 3 ^ 40 * 7934169 * 2
def baseEnd_7934169 : Nat := 4074042291002673260998927

theorem tailTrace_7934169 : CollatzResearch.WordTrace tailWord_7934169 prefixEnd_7934169 4074042291002673260998927 := by
  unfold tailWord_7934169
  simp only [CollatzResearch.WordTrace]
  refine ⟨289382917192868236029413561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192921944795245490686275707 289382917192868236029413561)
  ·
    refine ⟨217037187894651177022060171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289382917192868236029413561 217037187894651177022060171)
    ·
      refine ⟨325555781841976765533090257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217037187894651177022060171 325555781841976765533090257)
      ·
        refine ⟨244166836381482574149817693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325555781841976765533090257 244166836381482574149817693)
        ·
          refine ⟨91562563643055965306181635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244166836381482574149817693 91562563643055965306181635)
          ·
            refine ⟨137343845464583947959272453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91562563643055965306181635 137343845464583947959272453)
            ·
              refine ⟨25751971024609490242363585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137343845464583947959272453 25751971024609490242363585)
              ·
                refine ⟨19313978268457117681772689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25751971024609490242363585 19313978268457117681772689)
                ·
                  refine ⟨14485483701342838261329517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19313978268457117681772689 14485483701342838261329517)
                  ·
                    refine ⟨5432056388003564347998569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14485483701342838261329517 5432056388003564347998569)
                    ·
                      refine ⟨4074042291002673260998927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5432056388003564347998569 4074042291002673260998927)
                      ·
                        rfl

theorem cell23_7934169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 3, 2].length) (baseStart_7934169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934169 prefixEnd_7934169 := by exact prefixLift 7934169
  have htrace : WordTrace (prefixWord ++ tailWord_7934169) baseStart_7934169 baseEnd_7934169 := by
    simpa [prefixWord, tailWord_7934169, baseEnd_7934169] using wordTrace_append hprefix tailTrace_7934169
  have hstable : (prefixWord ++ tailWord_7934169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934169).length < 2 ^ (prefixWord ++ tailWord_7934169).sum := by decide
  have hdescent : baseEnd_7934169 < baseStart_7934169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934175 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 5, 6]
def baseStart_7934175 : Nat := 118140960795 + 7934175 * 2 ^ 59
def prefixEnd_7934175 : Nat := 4983230072969 + 3 ^ 40 * 7934175 * 2
def baseEnd_7934175 : Nat := 1358015123962200079174633

theorem tailTrace_7934175 : CollatzResearch.WordTrace tailWord_7934175 prefixEnd_7934175 1358015123962200079174633 := by
  unfold tailWord_7934175
  simp only [CollatzResearch.WordTrace]
  refine ⟨289383136030846499054131979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192922090687230999369421319 289383136030846499054131979)
  ·
    refine ⟨434074704046269748581197969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289383136030846499054131979 434074704046269748581197969)
    ·
      refine ⟨325556028034702311435898477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434074704046269748581197969 325556028034702311435898477)
      ·
        refine ⟨122083510513013366788461929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325556028034702311435898477 122083510513013366788461929)
        ·
          refine ⟨91562632884760025091346447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122083510513013366788461929 91562632884760025091346447)
          ·
            refine ⟨137343949327140037637019671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91562632884760025091346447 137343949327140037637019671)
            ·
              refine ⟨206015923990710056455529507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137343949327140037637019671 206015923990710056455529507)
              ·
                refine ⟨309023885986065084683294261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206015923990710056455529507 309023885986065084683294261)
                ·
                  refine ⟨28970989311193601689058837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 309023885986065084683294261 28970989311193601689058837)
                  ·
                    refine ⟨1358015123962200079174633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28970989311193601689058837 1358015123962200079174633)
                    ·
                      rfl

theorem cell23_7934175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 6].length) (baseStart_7934175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934175 prefixEnd_7934175 := by exact prefixLift 7934175
  have htrace : WordTrace (prefixWord ++ tailWord_7934175) baseStart_7934175 baseEnd_7934175 := by
    simpa [prefixWord, tailWord_7934175, baseEnd_7934175] using wordTrace_append hprefix tailTrace_7934175
  have hstable : (prefixWord ++ tailWord_7934175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934175).length < 2 ^ (prefixWord ++ tailWord_7934175).sum := by decide
  have hdescent : baseEnd_7934175 < baseStart_7934175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934176 : List Nat := [2, 1, 1, 3, 1, 3, 3, 4, 1, 1, 3]
def baseStart_7934176 : Nat := 118140960795 + 7934176 * 2 ^ 59
def prefixEnd_7934176 : Nat := 4983230072969 + 3 ^ 40 * 7934176 * 2
def baseEnd_7934176 : Nat := 4074045885367254733611395

theorem tailTrace_7934176 : CollatzResearch.WordTrace tailWord_7934176 prefixEnd_7934176 4074045885367254733611395 := by
  unfold tailWord_7934176
  simp only [CollatzResearch.WordTrace]
  refine ⟨144691586251921438112459191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192922115002561917483278921 144691586251921438112459191)
  ·
    refine ⟨217037379377882157168688787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144691586251921438112459191 217037379377882157168688787)
    ·
      refine ⟨325556069066823235753033181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217037379377882157168688787 325556069066823235753033181)
      ·
        refine ⟨122083525900058713407387443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325556069066823235753033181 122083525900058713407387443)
        ·
          refine ⟨183125288850088070111081165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122083525900058713407387443 183125288850088070111081165)
          ·
            refine ⟨68671983318783026291655437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183125288850088070111081165 68671983318783026291655437)
            ·
              refine ⟨25751993744543634859370789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68671983318783026291655437 25751993744543634859370789)
              ·
                refine ⟨4828498827101931536132023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25751993744543634859370789 4828498827101931536132023)
                ·
                  refine ⟨7242748240652897304198035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4828498827101931536132023 7242748240652897304198035)
                  ·
                    refine ⟨10864122360979345956297053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7242748240652897304198035 10864122360979345956297053)
                    ·
                      refine ⟨4074045885367254733611395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10864122360979345956297053 4074045885367254733611395)
                      ·
                        rfl

theorem cell23_7934176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_7934176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934176 prefixEnd_7934176 := by exact prefixLift 7934176
  have htrace : WordTrace (prefixWord ++ tailWord_7934176) baseStart_7934176 baseEnd_7934176 := by
    simpa [prefixWord, tailWord_7934176, baseEnd_7934176] using wordTrace_append hprefix tailTrace_7934176
  have hstable : (prefixWord ++ tailWord_7934176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934176).length < 2 ^ (prefixWord ++ tailWord_7934176).sum := by decide
  have hdescent : baseEnd_7934176 < baseStart_7934176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934205 : List Nat := [1, 4, 1, 1, 1, 1, 1, 13]
def baseStart_7934205 : Nat := 118140960795 + 7934205 * 2 ^ 59
def prefixEnd_7934205 : Nat := 4983230072969 + 3 ^ 40 * 7934205 * 2
def baseEnd_7934205 : Nat := 150891139863193893338843

theorem tailTrace_7934205 : CollatzResearch.WordTrace tailWord_7934205 prefixEnd_7934205 150891139863193893338843 := by
  unfold tailWord_7934205
  simp only [CollatzResearch.WordTrace]
  refine ⟨289384230220737814177724069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192922820147158542785149379 289384230220737814177724069)
  ·
    refine ⟨54259543166388340158323263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289384230220737814177724069 54259543166388340158323263)
    ·
      refine ⟨81389314749582510237484895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54259543166388340158323263 81389314749582510237484895)
      ·
        refine ⟨122083972124373765356227343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81389314749582510237484895 122083972124373765356227343)
        ·
          refine ⟨183125958186560648034341015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122083972124373765356227343 183125958186560648034341015)
          ·
            refine ⟨274688937279840972051511523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183125958186560648034341015 274688937279840972051511523)
            ·
              refine ⟨412033405919761458077267285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274688937279840972051511523 412033405919761458077267285)
              ·
                refine ⟨150891139863193893338843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 412033405919761458077267285 150891139863193893338843)
                ·
                  rfl

theorem cell23_7934205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 13].length) (baseStart_7934205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934205 prefixEnd_7934205 := by exact prefixLift 7934205
  have htrace : WordTrace (prefixWord ++ tailWord_7934205) baseStart_7934205 baseEnd_7934205 := by
    simpa [prefixWord, tailWord_7934205, baseEnd_7934205] using wordTrace_append hprefix tailTrace_7934205
  have hstable : (prefixWord ++ tailWord_7934205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934205).length < 2 ^ (prefixWord ++ tailWord_7934205).sum := by decide
  have hdescent : baseEnd_7934205 < baseStart_7934205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934210 : List Nat := [3, 4, 1, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_7934210 : Nat := 118140960795 + 7934210 * 2 ^ 59
def prefixEnd_7934210 : Nat := 4983230072969 + 3 ^ 40 * 7934210 * 2
def baseEnd_7934210 : Nat := 4074063343709507600586239

theorem tailTrace_7934210 : CollatzResearch.WordTrace tailWord_7934210 prefixEnd_7934210 4074063343709507600586239 := by
  unfold tailWord_7934210
  simp only [CollatzResearch.WordTrace]
  refine ⟨72346103146429925007914021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192922941723813133354437389 72346103146429925007914021)
  ·
    refine ⟨13564894339955610938983879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72346103146429925007914021 13564894339955610938983879)
    ·
      refine ⟨20347341509933416408475819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13564894339955610938983879 20347341509933416408475819)
      ·
        refine ⟨30521012264900124612713729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20347341509933416408475819 30521012264900124612713729)
        ·
          refine ⟨22890759198675093459535297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30521012264900124612713729 22890759198675093459535297)
          ·
            refine ⟨17168069399006320094651473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22890759198675093459535297 17168069399006320094651473)
            ·
              refine ⟨12876052049254740070988605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17168069399006320094651473 12876052049254740070988605)
              ·
                refine ⟨4828519518470527526620727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12876052049254740070988605 4828519518470527526620727)
                ·
                  refine ⟨7242779277705791289931091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4828519518470527526620727 7242779277705791289931091)
                  ·
                    refine ⟨10864168916558686934896637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7242779277705791289931091 10864168916558686934896637)
                    ·
                      refine ⟨4074063343709507600586239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10864168916558686934896637 4074063343709507600586239)
                      ·
                        rfl

theorem cell23_7934210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_7934210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934210 prefixEnd_7934210 := by exact prefixLift 7934210
  have htrace : WordTrace (prefixWord ++ tailWord_7934210) baseStart_7934210 baseEnd_7934210 := by
    simpa [prefixWord, tailWord_7934210, baseEnd_7934210] using wordTrace_append hprefix tailTrace_7934210
  have hstable : (prefixWord ++ tailWord_7934210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934210).length < 2 ^ (prefixWord ++ tailWord_7934210).sum := by decide
  have hdescent : baseEnd_7934210 < baseStart_7934210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934216 : List Nat := [2, 1, 3, 2, 3, 1, 4, 1, 1, 1, 4]
def baseStart_7934216 : Nat := 118140960795 + 7934216 * 2 ^ 59
def prefixEnd_7934216 : Nat := 4983230072969 + 3 ^ 40 * 7934216 * 2
def baseEnd_7934216 : Nat := 4074066424593434577111211

theorem tailTrace_7934216 : CollatzResearch.WordTrace tailWord_7934216 prefixEnd_7934216 4074066424593434577111211 := by
  unfold tailWord_7934216
  simp only [CollatzResearch.WordTrace]
  refine ⟨144692315711848981528187251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192923087615798642037583001 144692315711848981528187251)
  ·
    refine ⟨217038473567773472292280877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144692315711848981528187251 217038473567773472292280877)
    ·
      refine ⟨81389427587915052109605329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217038473567773472292280877 81389427587915052109605329)
      ·
        refine ⟨61042070690936289082203997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81389427587915052109605329 61042070690936289082203997)
        ·
          refine ⟨22890776509101108405826499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61042070690936289082203997 22890776509101108405826499)
          ·
            refine ⟨34336164763651662608739749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22890776509101108405826499 34336164763651662608739749)
            ·
              refine ⟨6438030893184686739138703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34336164763651662608739749 6438030893184686739138703)
              ·
                refine ⟨9657046339777030108708055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6438030893184686739138703 9657046339777030108708055)
                ·
                  refine ⟨14485569509665545163062083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9657046339777030108708055 14485569509665545163062083)
                  ·
                    refine ⟨21728354264498317744593125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14485569509665545163062083 21728354264498317744593125)
                    ·
                      refine ⟨4074066424593434577111211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21728354264498317744593125 4074066424593434577111211)
                      ·
                        rfl

theorem cell23_7934216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_7934216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934216 prefixEnd_7934216 := by exact prefixLift 7934216
  have htrace : WordTrace (prefixWord ++ tailWord_7934216) baseStart_7934216 baseEnd_7934216 := by
    simpa [prefixWord, tailWord_7934216, baseEnd_7934216] using wordTrace_append hprefix tailTrace_7934216
  have hstable : (prefixWord ++ tailWord_7934216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934216).length < 2 ^ (prefixWord ++ tailWord_7934216).sum := by decide
  have hdescent : baseEnd_7934216 < baseStart_7934216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934219 : List Nat := [1, 1, 1, 1, 5, 2, 3, 3, 1, 2, 3]
def baseStart_7934219 : Nat := 118140960795 + 7934219 * 2 ^ 59
def prefixEnd_7934219 : Nat := 4983230072969 + 3 ^ 40 * 7934219 * 2
def baseEnd_7934219 : Nat := 4074067965035398065373697

theorem tailTrace_7934219 : CollatzResearch.WordTrace tailWord_7934219 prefixEnd_7934219 4074067965035398065373697 := by
  unfold tailWord_7934219
  simp only [CollatzResearch.WordTrace]
  refine ⟨289384740842687094568733711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192923160561791396379155807 289384740842687094568733711)
  ·
    refine ⟨434077111264030641853100567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289384740842687094568733711 434077111264030641853100567)
    ·
      refine ⟨651115666896045962779650851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434077111264030641853100567 651115666896045962779650851)
      ·
        refine ⟨976673500344068944169476277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651115666896045962779650851 976673500344068944169476277)
        ·
          refine ⟨91563140657256463515888401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 976673500344068944169476277 91563140657256463515888401)
          ·
            refine ⟨68672355492942347636916301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91563140657256463515888401 68672355492942347636916301)
            ·
              refine ⟨25752133309853380363843613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68672355492942347636916301 25752133309853380363843613)
              ·
                refine ⟨9657049991195017636441355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25752133309853380363843613 9657049991195017636441355)
                ·
                  refine ⟨14485574986792526454662033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9657049991195017636441355 14485574986792526454662033)
                  ·
                    refine ⟨10864181240094394840996525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14485574986792526454662033 10864181240094394840996525)
                    ·
                      refine ⟨4074067965035398065373697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10864181240094394840996525 4074067965035398065373697)
                      ·
                        rfl

theorem cell23_7934219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 2, 3].length) (baseStart_7934219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934219 prefixEnd_7934219 := by exact prefixLift 7934219
  have htrace : WordTrace (prefixWord ++ tailWord_7934219) baseStart_7934219 baseEnd_7934219 := by
    simpa [prefixWord, tailWord_7934219, baseEnd_7934219] using wordTrace_append hprefix tailTrace_7934219
  have hstable : (prefixWord ++ tailWord_7934219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934219).length < 2 ^ (prefixWord ++ tailWord_7934219).sum := by decide
  have hdescent : baseEnd_7934219 < baseStart_7934219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934235 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 1, 9]
def baseStart_7934235 : Nat := 118140960795 + 7934235 * 2 ^ 59
def prefixEnd_7934235 : Nat := 4983230072969 + 3 ^ 40 * 7934235 * 2
def baseEnd_7934235 : Nat := 1358025393575290000924541

theorem tailTrace_7934235 : CollatzResearch.WordTrace tailWord_7934235 prefixEnd_7934235 1358025393575290000924541 := by
  unfold tailWord_7934235
  simp only [CollatzResearch.WordTrace]
  refine ⟨289385324410629129301316159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192923549607086086200877439 289385324410629129301316159)
  ·
    refine ⟨434077986615943693951974239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289385324410629129301316159 434077986615943693951974239)
    ·
      refine ⟨651116979923915540927961359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434077986615943693951974239 651116979923915540927961359)
      ·
        refine ⟨976675469885873311391942039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651116979923915540927961359 976675469885873311391942039)
        ·
          refine ⟨1465013204828809967087913059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976675469885873311391942039 1465013204828809967087913059)
          ·
            refine ⟨2197519807243214950631869589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465013204828809967087913059 2197519807243214950631869589)
            ·
              refine ⟨103008740964525700810868887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2197519807243214950631869589 103008740964525700810868887)
              ·
                refine ⟨154513111446788551216303331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103008740964525700810868887 154513111446788551216303331)
                ·
                  refine ⟨231769667170182826824454997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154513111446788551216303331 231769667170182826824454997)
                  ·
                    refine ⟨1358025393575290000924541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 231769667170182826824454997 1358025393575290000924541)
                    ·
                      rfl

theorem cell23_7934235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 9].length) (baseStart_7934235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934235 prefixEnd_7934235 := by exact prefixLift 7934235
  have htrace : WordTrace (prefixWord ++ tailWord_7934235) baseStart_7934235 baseEnd_7934235 := by
    simpa [prefixWord, tailWord_7934235, baseEnd_7934235] using wordTrace_append hprefix tailTrace_7934235
  have hstable : (prefixWord ++ tailWord_7934235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934235).length < 2 ^ (prefixWord ++ tailWord_7934235).sum := by decide
  have hdescent : baseEnd_7934235 < baseStart_7934235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934300 : List Nat := [2, 2, 4, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_7934300 : Nat := 118140960795 + 7934300 * 2 ^ 59
def prefixEnd_7934300 : Nat := 4983230072969 + 3 ^ 40 * 7934300 * 2
def baseEnd_7934300 : Nat := 4074109556968412248460825

theorem tailTrace_7934300 : CollatzResearch.WordTrace tailWord_7934300 prefixEnd_7934300 4074109556968412248460825 := by
  unfold tailWord_7934300
  simp only [CollatzResearch.WordTrace]
  refine ⟨144693847577696822701216177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192925130103595763601621569 144693847577696822701216177)
  ·
    refine ⟨108520385683272617025912133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144693847577696822701216177 108520385683272617025912133)
    ·
      refine ⟨20347572315613615692358525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108520385683272617025912133 20347572315613615692358525)
      ·
        refine ⟨7630339618355105884634447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20347572315613615692358525 7630339618355105884634447)
        ·
          refine ⟨11445509427532658826951671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7630339618355105884634447 11445509427532658826951671)
          ·
            refine ⟨17168264141298988240427507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11445509427532658826951671 17168264141298988240427507)
            ·
              refine ⟨25752396211948482360641261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17168264141298988240427507 25752396211948482360641261)
              ·
                refine ⟨9657148579480680885240473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25752396211948482360641261 9657148579480680885240473)
                ·
                  refine ⟨7242861434610510663930355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9657148579480680885240473 7242861434610510663930355)
                  ·
                    refine ⟨10864292151915765995895533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7242861434610510663930355 10864292151915765995895533)
                    ·
                      refine ⟨4074109556968412248460825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10864292151915765995895533 4074109556968412248460825)
                      ·
                        rfl

theorem cell23_7934300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_7934300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934300 prefixEnd_7934300 := by exact prefixLift 7934300
  have htrace : WordTrace (prefixWord ++ tailWord_7934300) baseStart_7934300 baseEnd_7934300 := by
    simpa [prefixWord, tailWord_7934300, baseEnd_7934300] using wordTrace_append hprefix tailTrace_7934300
  have hstable : (prefixWord ++ tailWord_7934300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934300).length < 2 ^ (prefixWord ++ tailWord_7934300).sum := by decide
  have hdescent : baseEnd_7934300 < baseStart_7934300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934329 : List Nat := [1, 2, 1, 3, 2, 1, 1, 7, 5]
def baseStart_7934329 : Nat := 118140960795 + 7934329 * 2 ^ 59
def prefixEnd_7934329 : Nat := 4983230072969 + 3 ^ 40 * 7934329 * 2
def baseEnd_7934329 : Nat := 452680494211932514999799

theorem tailTrace_7934329 : CollatzResearch.WordTrace tailWord_7934329 prefixEnd_7934329 452680494211932514999799 := by
  unfold tailWord_7934329
  simp only [CollatzResearch.WordTrace]
  refine ⟨289388752872288583355238041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192925835248192388903492027 289388752872288583355238041)
  ·
    refine ⟨217041564654216437516428531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289388752872288583355238041 217041564654216437516428531)
    ·
      refine ⟨325562346981324656274642797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217041564654216437516428531 325562346981324656274642797)
      ·
        refine ⟨122085880117996746102991049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325562346981324656274642797 122085880117996746102991049)
        ·
          refine ⟨91564410088497559577243287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122085880117996746102991049 91564410088497559577243287)
          ·
            refine ⟨137346615132746339365864931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91564410088497559577243287 137346615132746339365864931)
            ·
              refine ⟨206019922699119509048797397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137346615132746339365864931 206019922699119509048797397)
              ·
                refine ⟨4828591938260613493331189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 206019922699119509048797397 4828591938260613493331189)
                ·
                  refine ⟨452680494211932514999799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4828591938260613493331189 452680494211932514999799)
                  ·
                    rfl

theorem cell23_7934329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 5].length) (baseStart_7934329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934329 prefixEnd_7934329 := by exact prefixLift 7934329
  have htrace : WordTrace (prefixWord ++ tailWord_7934329) baseStart_7934329 baseEnd_7934329 := by
    simpa [prefixWord, tailWord_7934329, baseEnd_7934329] using wordTrace_append hprefix tailTrace_7934329
  have hstable : (prefixWord ++ tailWord_7934329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934329).length < 2 ^ (prefixWord ++ tailWord_7934329).sum := by decide
  have hdescent : baseEnd_7934329 < baseStart_7934329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934376 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 1, 7]
def baseStart_7934376 : Nat := 118140960795 + 7934376 * 2 ^ 59
def prefixEnd_7934376 : Nat := 4983230072969 + 3 ^ 40 * 7934376 * 2
def baseEnd_7934376 : Nat := 1358049527166051317036825

theorem tailTrace_7934376 : CollatzResearch.WordTrace tailWord_7934376 prefixEnd_7934376 1358049527166051317036825 := by
  unfold tailWord_7934376
  simp only [CollatzResearch.WordTrace]
  refine ⟨144695233551559155191099491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192926978068745540254799321 144695233551559155191099491)
  ·
    refine ⟨217042850327338732786649237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144695233551559155191099491 217042850327338732786649237)
    ·
      refine ⟨10173883609094003099374183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 217042850327338732786649237 10173883609094003099374183)
      ·
        refine ⟨15260825413641004649061275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10173883609094003099374183 15260825413641004649061275)
        ·
          refine ⟨22891238120461506973591913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15260825413641004649061275 22891238120461506973591913)
          ·
            refine ⟨17168428590346130230193935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22891238120461506973591913 17168428590346130230193935)
            ·
              refine ⟨25752642885519195345290903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17168428590346130230193935 25752642885519195345290903)
              ·
                refine ⟨38628964328278793017936355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25752642885519195345290903 38628964328278793017936355)
                ·
                  refine ⟨57943446492418189526904533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38628964328278793017936355 57943446492418189526904533)
                  ·
                    refine ⟨1358049527166051317036825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57943446492418189526904533 1358049527166051317036825)
                    ·
                      rfl

theorem cell23_7934376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_7934376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934376 prefixEnd_7934376 := by exact prefixLift 7934376
  have htrace : WordTrace (prefixWord ++ tailWord_7934376) baseStart_7934376 baseEnd_7934376 := by
    simpa [prefixWord, tailWord_7934376, baseEnd_7934376] using wordTrace_append hprefix tailTrace_7934376
  have hstable : (prefixWord ++ tailWord_7934376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934376).length < 2 ^ (prefixWord ++ tailWord_7934376).sum := by decide
  have hdescent : baseEnd_7934376 < baseStart_7934376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934440 : List Nat := [2, 1, 4, 1, 1, 5, 1, 3, 1, 4]
def baseStart_7934440 : Nat := 118140960795 + 7934440 * 2 ^ 59
def prefixEnd_7934440 : Nat := 4983230072969 + 3 ^ 40 * 7934440 * 2
def baseEnd_7934440 : Nat := 1358060481420013900236727

theorem tailTrace_7934440 : CollatzResearch.WordTrace tailWord_7934440 prefixEnd_7934440 1358060481420013900236727 := by
  unfold tailWord_7934440
  simp only [CollatzResearch.WordTrace]
  refine ⟨144696400687443224656264387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192928534249924299541685849 144696400687443224656264387)
  ·
    refine ⟨217044601031164836984396581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144696400687443224656264387 217044601031164836984396581)
    ·
      refine ⟨40695862693343406934574359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217044601031164836984396581 40695862693343406934574359)
      ·
        refine ⟨61043794040015110401861539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40695862693343406934574359 61043794040015110401861539)
        ·
          refine ⟨91565691060022665602792309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61043794040015110401861539 91565691060022665602792309)
          ·
            refine ⟨8584283536877124900261779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91565691060022665602792309 8584283536877124900261779)
            ·
              refine ⟨12876425305315687350392669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8584283536877124900261779 12876425305315687350392669)
              ·
                refine ⟨4828659489493382756397251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12876425305315687350392669 4828659489493382756397251)
                ·
                  refine ⟨7242989234240074134595877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4828659489493382756397251 7242989234240074134595877)
                  ·
                    refine ⟨1358060481420013900236727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7242989234240074134595877 1358060481420013900236727)
                    ·
                      rfl

theorem cell23_7934440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_7934440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934440 prefixEnd_7934440 := by exact prefixLift 7934440
  have htrace : WordTrace (prefixWord ++ tailWord_7934440) baseStart_7934440 baseEnd_7934440 := by
    simpa [prefixWord, tailWord_7934440, baseEnd_7934440] using wordTrace_append hprefix tailTrace_7934440
  have hstable : (prefixWord ++ tailWord_7934440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934440).length < 2 ^ (prefixWord ++ tailWord_7934440).sum := by decide
  have hdescent : baseEnd_7934440 < baseStart_7934440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934489 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 2, 6, 3]
def baseStart_7934489 : Nat := 118140960795 + 7934489 * 2 ^ 59
def prefixEnd_7934489 : Nat := 4983230072969 + 3 ^ 40 * 7934489 * 2
def baseEnd_7934489 : Nat := 4074206604812112008997455

theorem tailTrace_7934489 : CollatzResearch.WordTrace tailWord_7934489 prefixEnd_7934489 4074206604812112008997455 := by
  unfold tailWord_7934489
  simp only [CollatzResearch.WordTrace]
  refine ⟨289394588551708930681062521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192929725701139287120708347 289394588551708930681062521)
  ·
    refine ⟨217045941413781698010796891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289394588551708930681062521 217045941413781698010796891)
    ·
      refine ⟨325568912120672547016195337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217045941413781698010796891 325568912120672547016195337)
      ·
        refine ⟨244176684090504410262146503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325568912120672547016195337 244176684090504410262146503)
        ·
          refine ⟨366265026135756615393219755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244176684090504410262146503 366265026135756615393219755)
          ·
            refine ⟨549397539203634923089829633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366265026135756615393219755 549397539203634923089829633)
            ·
              refine ⟨412048154402726192317372225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549397539203634923089829633 412048154402726192317372225)
              ·
                refine ⟨309036115802044644238029169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412048154402726192317372225 309036115802044644238029169)
                ·
                  refine ⟨231777086851533483178521877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309036115802044644238029169 231777086851533483178521877)
                  ·
                    refine ⟨10864550946165632023993213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 231777086851533483178521877 10864550946165632023993213)
                    ·
                      refine ⟨4074206604812112008997455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10864550946165632023993213 4074206604812112008997455)
                      ·
                        rfl

theorem cell23_7934489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_7934489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934489 prefixEnd_7934489 := by exact prefixLift 7934489
  have htrace : WordTrace (prefixWord ++ tailWord_7934489) baseStart_7934489 baseEnd_7934489 := by
    simpa [prefixWord, tailWord_7934489, baseEnd_7934489] using wordTrace_append hprefix tailTrace_7934489
  have hstable : (prefixWord ++ tailWord_7934489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934489).length < 2 ^ (prefixWord ++ tailWord_7934489).sum := by decide
  have hdescent : baseEnd_7934489 < baseStart_7934489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934579 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 5]
def baseStart_7934579 : Nat := 118140960795 + 7934579 * 2 ^ 59
def prefixEnd_7934579 : Nat := 4983230072969 + 3 ^ 40 * 7934579 * 2
def baseEnd_7934579 : Nat := 4074252818071016656872041

theorem tailTrace_7934579 : CollatzResearch.WordTrace tailWord_7934579 prefixEnd_7934579 4074252818071016656872041 := by
  unfold tailWord_7934579
  simp only [CollatzResearch.WordTrace]
  refine ⟨289397871121382876051838791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192931914080921917367892527 289397871121382876051838791)
  ·
    refine ⟨434096806682074314077758187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289397871121382876051838791 434096806682074314077758187)
    ·
      refine ⟨651145210023111471116637281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434096806682074314077758187 651145210023111471116637281)
      ·
        refine ⟨488358907517333603337477961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 651145210023111471116637281 488358907517333603337477961)
        ·
          refine ⟨366269180638000202503108471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488358907517333603337477961 366269180638000202503108471)
          ·
            refine ⟨549403770957000303754662707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366269180638000202503108471 549403770957000303754662707)
            ·
              refine ⟨824105656435500455631994061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549403770957000303754662707 824105656435500455631994061)
              ·
                refine ⟨309039621163312670861997773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 824105656435500455631994061 309039621163312670861997773)
                ·
                  refine ⟨115889857936242251573249165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309039621163312670861997773 115889857936242251573249165)
                  ·
                    refine ⟨43458696726090844339968437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115889857936242251573249165 43458696726090844339968437)
                    ·
                      refine ⟨4074252818071016656872041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43458696726090844339968437 4074252818071016656872041)
                      ·
                        rfl

theorem cell23_7934579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_7934579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934579 prefixEnd_7934579 := by exact prefixLift 7934579
  have htrace : WordTrace (prefixWord ++ tailWord_7934579) baseStart_7934579 baseEnd_7934579 := by
    simpa [prefixWord, tailWord_7934579, baseEnd_7934579] using wordTrace_append hprefix tailTrace_7934579
  have hstable : (prefixWord ++ tailWord_7934579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934579).length < 2 ^ (prefixWord ++ tailWord_7934579).sum := by decide
  have hdescent : baseEnd_7934579 < baseStart_7934579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934594 : List Nat := [3, 4, 3, 1, 1, 2, 2, 7]
def baseStart_7934594 : Nat := 118140960795 + 7934594 * 2 ^ 59
def prefixEnd_7934594 : Nat := 4983230072969 + 3 ^ 40 * 7934594 * 2
def baseEnd_7934594 : Nat := 150898537788179040673499

theorem tailTrace_7934594 : CollatzResearch.WordTrace tailWord_7934594 prefixEnd_7934594 150898537788179040673499 := by
  unfold tailWord_7934594
  simp only [CollatzResearch.WordTrace]
  refine ⟨72349604554082133403408709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192932278810885689075756557 72349604554082133403408709)
  ·
    refine ⟨13565550853890400013139133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72349604554082133403408709 13565550853890400013139133)
    ·
      refine ⟨5087081570208900004927175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13565550853890400013139133 5087081570208900004927175)
      ·
        refine ⟨7630622355313350007390763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5087081570208900004927175 7630622355313350007390763)
        ·
          refine ⟨11445933532970025011086145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7630622355313350007390763 11445933532970025011086145)
          ·
            refine ⟨8584450149727518758314609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11445933532970025011086145 8584450149727518758314609)
            ·
              refine ⟨6438337612295639068735957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8584450149727518758314609 6438337612295639068735957)
              ·
                refine ⟨150898537788179040673499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6438337612295639068735957 150898537788179040673499)
                ·
                  rfl

theorem cell23_7934594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 7].length) (baseStart_7934594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934594 prefixEnd_7934594 := by exact prefixLift 7934594
  have htrace : WordTrace (prefixWord ++ tailWord_7934594) baseStart_7934594 baseEnd_7934594 := by
    simpa [prefixWord, tailWord_7934594, baseEnd_7934594] using wordTrace_append hprefix tailTrace_7934594
  have hstable : (prefixWord ++ tailWord_7934594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934594).length < 2 ^ (prefixWord ++ tailWord_7934594).sum := by decide
  have hdescent : baseEnd_7934594 < baseStart_7934594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934619 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 8]
def baseStart_7934619 : Nat := 118140960795 + 7934619 * 2 ^ 59
def prefixEnd_7934619 : Nat := 4983230072969 + 3 ^ 40 * 7934619 * 2
def baseEnd_7934619 : Nat := 4074273357297196500371857

theorem tailTrace_7934619 : CollatzResearch.WordTrace tailWord_7934619 prefixEnd_7934619 4074273357297196500371857 := by
  unfold tailWord_7934619
  simp only [CollatzResearch.WordTrace]
  refine ⟨289399330041237962883294911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192932886694158641922196607 289399330041237962883294911)
  ·
    refine ⟨434098995061856944324942367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289399330041237962883294911 434098995061856944324942367)
    ·
      refine ⟨651148492592785416487413551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434098995061856944324942367 651148492592785416487413551)
      ·
        refine ⟨976722738889178124731120327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651148492592785416487413551 976722738889178124731120327)
        ·
          refine ⟨1465084108333767187096680491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976722738889178124731120327 1465084108333767187096680491)
          ·
            refine ⟨2197626162500650780645020737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465084108333767187096680491 2197626162500650780645020737)
            ·
              refine ⟨1648219621875488085483765553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2197626162500650780645020737 1648219621875488085483765553)
              ·
                refine ⟨1236164716406616064112824165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1648219621875488085483765553 1236164716406616064112824165)
                ·
                  refine ⟨231780884326240512021154531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1236164716406616064112824165 231780884326240512021154531)
                  ·
                    refine ⟨347671326489360768031731797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 231780884326240512021154531 347671326489360768031731797)
                    ·
                      refine ⟨4074273357297196500371857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 347671326489360768031731797 4074273357297196500371857)
                      ·
                        rfl

theorem cell23_7934619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 8].length) (baseStart_7934619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934619 prefixEnd_7934619 := by exact prefixLift 7934619
  have htrace : WordTrace (prefixWord ++ tailWord_7934619) baseStart_7934619 baseEnd_7934619 := by
    simpa [prefixWord, tailWord_7934619, baseEnd_7934619] using wordTrace_append hprefix tailTrace_7934619
  have hstable : (prefixWord ++ tailWord_7934619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934619).length < 2 ^ (prefixWord ++ tailWord_7934619).sum := by decide
  have hdescent : baseEnd_7934619 < baseStart_7934619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934684 : List Nat := [2, 2, 5, 1, 1, 3, 2, 2, 5]
def baseStart_7934684 : Nat := 118140960795 + 7934684 * 2 ^ 59
def prefixEnd_7934684 : Nat := 4983230072969 + 3 ^ 40 * 7934684 * 2
def baseEnd_7934684 : Nat := 452700748171082082895451

theorem tailTrace_7934684 : CollatzResearch.WordTrace tailWord_7934684 prefixEnd_7934684 452700748171082082895451 := by
  unfold tailWord_7934684
  simp only [CollatzResearch.WordTrace]
  refine ⟨144700850393001239492205553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192934467190668319322940737 144700850393001239492205553)
  ·
    refine ⟨108525637794750929619154165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144700850393001239492205553 108525637794750929619154165)
    ·
      refine ⟨10174278543257899651795703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108525637794750929619154165 10174278543257899651795703)
      ·
        refine ⟨15261417814886849477693555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10174278543257899651795703 15261417814886849477693555)
        ·
          refine ⟨22892126722330274216540333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15261417814886849477693555 22892126722330274216540333)
          ·
            refine ⟨8584547520873852831202625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22892126722330274216540333 8584547520873852831202625)
            ·
              refine ⟨6438410640655389623401969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8584547520873852831202625 6438410640655389623401969)
              ·
                refine ⟨4828807980491542217551477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6438410640655389623401969 4828807980491542217551477)
                ·
                  refine ⟨452700748171082082895451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4828807980491542217551477 452700748171082082895451)
                  ·
                    rfl

theorem cell23_7934684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 5].length) (baseStart_7934684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934684 prefixEnd_7934684 := by exact prefixLift 7934684
  have htrace : WordTrace (prefixWord ++ tailWord_7934684) baseStart_7934684 baseEnd_7934684 := by
    simpa [prefixWord, tailWord_7934684, baseEnd_7934684] using wordTrace_append hprefix tailTrace_7934684
  have hstable : (prefixWord ++ tailWord_7934684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934684).length < 2 ^ (prefixWord ++ tailWord_7934684).sum := by decide
  have hdescent : baseEnd_7934684 < baseStart_7934684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934710 : List Nat := [5, 1, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_7934710 : Nat := 118140960795 + 7934710 * 2 ^ 59
def prefixEnd_7934710 : Nat := 4983230072969 + 3 ^ 40 * 7934710 * 2
def baseEnd_7934710 : Nat := 1358106694678918548111313

theorem tailTrace_7934710 : CollatzResearch.WordTrace tailWord_7934710 prefixEnd_7934710 1358106694678918548111313 := by
  unfold tailWord_7934710
  simp only [CollatzResearch.WordTrace]
  refine ⟨18087665567744267839053599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192935099389272190283238389 18087665567744267839053599)
  ·
    refine ⟨27131498351616401758580399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18087665567744267839053599 27131498351616401758580399)
    ·
      refine ⟨40697247527424602637870599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27131498351616401758580399 40697247527424602637870599)
      ·
        refine ⟨61045871291136903956805899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40697247527424602637870599 61045871291136903956805899)
        ·
          refine ⟨91568806936705355935208849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61045871291136903956805899 91568806936705355935208849)
          ·
            refine ⟨68676605202529016951406637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91568806936705355935208849 68676605202529016951406637)
            ·
              refine ⟨25753726950948381356777489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68676605202529016951406637 25753726950948381356777489)
              ·
                refine ⟨19315295213211286017583117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25753726950948381356777489 19315295213211286017583117)
                ·
                  refine ⟨7243235704954232256593669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19315295213211286017583117 7243235704954232256593669)
                  ·
                    refine ⟨1358106694678918548111313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7243235704954232256593669 1358106694678918548111313)
                    ·
                      rfl

theorem cell23_7934710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_7934710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934710 prefixEnd_7934710 := by exact prefixLift 7934710
  have htrace : WordTrace (prefixWord ++ tailWord_7934710) baseStart_7934710 baseEnd_7934710 := by
    simpa [prefixWord, tailWord_7934710, baseEnd_7934710] using wordTrace_append hprefix tailTrace_7934710
  have hstable : (prefixWord ++ tailWord_7934710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934710).length < 2 ^ (prefixWord ++ tailWord_7934710).sum := by decide
  have hdescent : baseEnd_7934710 < baseStart_7934710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934727 : List Nat := [1, 1, 4, 4, 1, 1, 1, 5, 1, 4]
def baseStart_7934727 : Nat := 118140960795 + 7934727 * 2 ^ 59
def prefixEnd_7934727 : Nat := 4983230072969 + 3 ^ 40 * 7934727 * 2
def baseEnd_7934727 : Nat := 1358109604402627359273787

theorem tailTrace_7934727 : CollatzResearch.WordTrace tailWord_7934727 prefixEnd_7934727 1358109604402627359273787 := by
  unfold tailWord_7934727
  simp only [CollatzResearch.WordTrace]
  refine ⟨289403269124846697328226435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192935512749897798218817623 289403269124846697328226435)
  ·
    refine ⟨434104903687270045992339653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289403269124846697328226435 434104903687270045992339653)
    ·
      refine ⟨81394669441363133623563685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 434104903687270045992339653 81394669441363133623563685)
      ·
        refine ⟨15261500520255587554418191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81394669441363133623563685 15261500520255587554418191)
        ·
          refine ⟨22892250780383381331627287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15261500520255587554418191 22892250780383381331627287)
          ·
            refine ⟨34338376170575071997440931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22892250780383381331627287 34338376170575071997440931)
            ·
              refine ⟨51507564255862607996161397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34338376170575071997440931 51507564255862607996161397)
              ·
                refine ⟨4828834148987119499640131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51507564255862607996161397 4828834148987119499640131)
                ·
                  refine ⟨7243251223480679249460197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4828834148987119499640131 7243251223480679249460197)
                  ·
                    refine ⟨1358109604402627359273787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7243251223480679249460197 1358109604402627359273787)
                    ·
                      rfl

theorem cell23_7934727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_7934727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934727 prefixEnd_7934727 := by exact prefixLift 7934727
  have htrace : WordTrace (prefixWord ++ tailWord_7934727) baseStart_7934727 baseEnd_7934727 := by
    simpa [prefixWord, tailWord_7934727, baseEnd_7934727] using wordTrace_append hprefix tailTrace_7934727
  have hstable : (prefixWord ++ tailWord_7934727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934727).length < 2 ^ (prefixWord ++ tailWord_7934727).sum := by decide
  have hdescent : baseEnd_7934727 < baseStart_7934727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934760 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_7934760 : Nat := 118140960795 + 7934760 * 2 ^ 59
def prefixEnd_7934760 : Nat := 4983230072969 + 3 ^ 40 * 7934760 * 2
def baseEnd_7934760 : Nat := 4074345758069480448708709

theorem tailTrace_7934760 : CollatzResearch.WordTrace tailWord_7934760 prefixEnd_7934760 4074345758069480448708709 := by
  unfold tailWord_7934760
  simp only [CollatzResearch.WordTrace]
  refine ⟨144702236366863571982088867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192936315155818095976118489 144702236366863571982088867)
  ·
    refine ⟨217053354550295357973133301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144702236366863571982088867 217053354550295357973133301)
    ·
      refine ⟨20348751989090189809981247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217053354550295357973133301 20348751989090189809981247)
      ·
        refine ⟨30523127983635284714971871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20348751989090189809981247 30523127983635284714971871)
        ·
          refine ⟨45784691975452927072457807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30523127983635284714971871 45784691975452927072457807)
          ·
            refine ⟨68677037963179390608686711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45784691975452927072457807 68677037963179390608686711)
            ·
              refine ⟨103015556944769085913030067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68677037963179390608686711 103015556944769085913030067)
              ·
                refine ⟨154523335417153628869545101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103015556944769085913030067 154523335417153628869545101)
                ·
                  refine ⟨57946250781432610826079413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154523335417153628869545101 57946250781432610826079413)
                  ·
                    refine ⟨5432461010759307264944945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57946250781432610826079413 5432461010759307264944945)
                    ·
                      refine ⟨4074345758069480448708709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5432461010759307264944945 4074345758069480448708709)
                      ·
                        rfl

theorem cell23_7934760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_7934760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934760 prefixEnd_7934760 := by exact prefixLift 7934760
  have htrace : WordTrace (prefixWord ++ tailWord_7934760) baseStart_7934760 baseEnd_7934760 := by
    simpa [prefixWord, tailWord_7934760, baseEnd_7934760] using wordTrace_append hprefix tailTrace_7934760
  have hstable : (prefixWord ++ tailWord_7934760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934760).length < 2 ^ (prefixWord ++ tailWord_7934760).sum := by decide
  have hdescent : baseEnd_7934760 < baseStart_7934760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934770 : List Nat := [3, 2, 1, 1, 3, 1, 4, 2, 1, 5]
def baseStart_7934770 : Nat := 118140960795 + 7934770 * 2 ^ 59
def prefixEnd_7934770 : Nat := 4983230072969 + 3 ^ 40 * 7934770 * 2
def baseEnd_7934770 : Nat := 1358116964292008469861221

theorem tailTrace_7934770 : CollatzResearch.WordTrace tailWord_7934770 prefixEnd_7934770 1358116964292008469861221 := by
  unfold tailWord_7934770
  simp only [CollatzResearch.WordTrace]
  refine ⟨72351209365922728918010441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192936558309127277114694509 72351209365922728918010441)
  ·
    refine ⟨54263407024442046688507831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72351209365922728918010441 54263407024442046688507831)
    ·
      refine ⟨81395110536663070032761747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54263407024442046688507831 81395110536663070032761747)
      ·
        refine ⟨122092665804994605049142621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81395110536663070032761747 122092665804994605049142621)
        ·
          refine ⟨45784749676872976893428483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122092665804994605049142621 45784749676872976893428483)
          ·
            refine ⟨68677124515309465340142725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45784749676872976893428483 68677124515309465340142725)
            ·
              refine ⟨12876960846620524751276761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68677124515309465340142725 12876960846620524751276761)
              ·
                refine ⟨9657720634965393563457571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12876960846620524751276761 9657720634965393563457571)
                ·
                  refine ⟨14486580952448090345186357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9657720634965393563457571 14486580952448090345186357)
                  ·
                    refine ⟨1358116964292008469861221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14486580952448090345186357 1358116964292008469861221)
                    ·
                      rfl

theorem cell23_7934770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_7934770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934770 prefixEnd_7934770 := by exact prefixLift 7934770
  have htrace : WordTrace (prefixWord ++ tailWord_7934770) baseStart_7934770 baseEnd_7934770 := by
    simpa [prefixWord, tailWord_7934770, baseEnd_7934770] using wordTrace_append hprefix tailTrace_7934770
  have hstable : (prefixWord ++ tailWord_7934770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934770).length < 2 ^ (prefixWord ++ tailWord_7934770).sum := by decide
  have hdescent : baseEnd_7934770 < baseStart_7934770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934793 : List Nat := [1, 2, 1, 1, 2, 5, 1, 3, 1, 1, 5]
def baseStart_7934793 : Nat := 118140960795 + 7934793 * 2 ^ 59
def prefixEnd_7934793 : Nat := 4983230072969 + 3 ^ 40 * 7934793 * 2
def baseEnd_7934793 : Nat := 4074362702931078819596057

theorem tailTrace_7934793 : CollatzResearch.WordTrace tailWord_7934793 prefixEnd_7934793 4074362702931078819596057 := by
  unfold tailWord_7934793
  simp only [CollatzResearch.WordTrace]
  refine ⟨289405676342607590600129033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192937117561738393733419355 289405676342607590600129033)
  ·
    refine ⟨217054257256955692950096775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289405676342607590600129033 217054257256955692950096775)
    ·
      refine ⟨325581385885433539425145163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217054257256955692950096775 325581385885433539425145163)
      ·
        refine ⟨488372078828150309137717745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325581385885433539425145163 488372078828150309137717745)
        ·
          refine ⟨366279059121112731853288309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488372078828150309137717745 366279059121112731853288309)
          ·
            refine ⟨34338661792604318611245779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 366279059121112731853288309 34338661792604318611245779)
            ·
              refine ⟨51507992688906477916868669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34338661792604318611245779 51507992688906477916868669)
              ·
                refine ⟨19315497258339929218825751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51507992688906477916868669 19315497258339929218825751)
                ·
                  refine ⟨28973245887509893828238627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19315497258339929218825751 28973245887509893828238627)
                  ·
                    refine ⟨43459868831264840742357941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28973245887509893828238627 43459868831264840742357941)
                    ·
                      refine ⟨4074362702931078819596057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43459868831264840742357941 4074362702931078819596057)
                      ·
                        rfl

theorem cell23_7934793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 1, 5].length) (baseStart_7934793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934793 prefixEnd_7934793 := by exact prefixLift 7934793
  have htrace : WordTrace (prefixWord ++ tailWord_7934793) baseStart_7934793 baseEnd_7934793 := by
    simpa [prefixWord, tailWord_7934793, baseEnd_7934793] using wordTrace_append hprefix tailTrace_7934793
  have hstable : (prefixWord ++ tailWord_7934793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934793).length < 2 ^ (prefixWord ++ tailWord_7934793).sum := by decide
  have hdescent : baseEnd_7934793 < baseStart_7934793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934801 : List Nat := [1, 2, 2, 1, 6, 1, 3, 2, 1, 1, 3]
def baseStart_7934801 : Nat := 118140960795 + 7934801 * 2 ^ 59
def prefixEnd_7934801 : Nat := 4983230072969 + 3 ^ 40 * 7934801 * 2
def baseEnd_7934801 : Nat := 4074366810776314788296021

theorem tailTrace_7934801 : CollatzResearch.WordTrace tailWord_7934801 prefixEnd_7934801 4074366810776314788296021 := by
  unfold tailWord_7934801
  simp only [CollatzResearch.WordTrace]
  refine ⟨289405968126578607966420257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192937312084385738644280171 289405968126578607966420257)
  ·
    refine ⟨217054476094933955974815193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289405968126578607966420257 217054476094933955974815193)
    ·
      refine ⟨162790857071200466981111395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217054476094933955974815193 162790857071200466981111395)
      ·
        refine ⟨244186285606800700471667093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162790857071200466981111395 244186285606800700471667093)
        ·
          refine ⟨11446232137818782834609395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 244186285606800700471667093 11446232137818782834609395)
          ·
            refine ⟨17169348206728174251914093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11446232137818782834609395 17169348206728174251914093)
            ·
              refine ⟨6438505577523065344467785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17169348206728174251914093 6438505577523065344467785)
              ·
                refine ⟨4828879183142299008350839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6438505577523065344467785 4828879183142299008350839)
                ·
                  refine ⟨7243318774713448512526259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4828879183142299008350839 7243318774713448512526259)
                  ·
                    refine ⟨10864978162070172768789389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7243318774713448512526259 10864978162070172768789389)
                    ·
                      refine ⟨4074366810776314788296021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10864978162070172768789389 4074366810776314788296021)
                      ·
                        rfl

theorem cell23_7934801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 1, 1, 3].length) (baseStart_7934801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934801 prefixEnd_7934801 := by exact prefixLift 7934801
  have htrace : WordTrace (prefixWord ++ tailWord_7934801) baseStart_7934801 baseEnd_7934801 := by
    simpa [prefixWord, tailWord_7934801, baseEnd_7934801] using wordTrace_append hprefix tailTrace_7934801
  have hstable : (prefixWord ++ tailWord_7934801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934801).length < 2 ^ (prefixWord ++ tailWord_7934801).sum := by decide
  have hdescent : baseEnd_7934801 < baseStart_7934801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934840 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 4, 1, 3]
def baseStart_7934840 : Nat := 118140960795 + 7934840 * 2 ^ 59
def prefixEnd_7934840 : Nat := 4983230072969 + 3 ^ 40 * 7934840 * 2
def baseEnd_7934840 : Nat := 4074386836521840135708341

theorem tailTrace_7934840 : CollatzResearch.WordTrace tailWord_7934840 prefixEnd_7934840 4074386836521840135708341 := by
  unfold tailWord_7934840
  simp only [CollatzResearch.WordTrace]
  refine ⟨144703695286718658813544987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192938260382291545084726649 144703695286718658813544987)
  ·
    refine ⟨217055542930077988220317481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144703695286718658813544987 217055542930077988220317481)
    ·
      refine ⟨162791657197558491165238111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217055542930077988220317481 162791657197558491165238111)
      ·
        refine ⟨244187485796337736747857167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162791657197558491165238111 244187485796337736747857167)
        ·
          refine ⟨366281228694506605121785751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244187485796337736747857167 366281228694506605121785751)
          ·
            refine ⟨549421843041759907682678627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366281228694506605121785751 549421843041759907682678627)
            ·
              refine ⟨824132764562639861524017941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549421843041759907682678627 824132764562639861524017941)
              ·
                refine ⟨38631223338873743508938341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 824132764562639861524017941 38631223338873743508938341)
                ·
                  refine ⟨7243354376038826907925939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38631223338873743508938341 7243354376038826907925939)
                  ·
                    refine ⟨10865031564058240361888909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7243354376038826907925939 10865031564058240361888909)
                    ·
                      refine ⟨4074386836521840135708341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10865031564058240361888909 4074386836521840135708341)
                      ·
                        rfl

theorem cell23_7934840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 4, 1, 3].length) (baseStart_7934840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934840 prefixEnd_7934840 := by exact prefixLift 7934840
  have htrace : WordTrace (prefixWord ++ tailWord_7934840) baseStart_7934840 baseEnd_7934840 := by
    simpa [prefixWord, tailWord_7934840, baseEnd_7934840] using wordTrace_append hprefix tailTrace_7934840
  have hstable : (prefixWord ++ tailWord_7934840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934840).length < 2 ^ (prefixWord ++ tailWord_7934840).sum := by decide
  have hdescent : baseEnd_7934840 < baseStart_7934840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934857 : List Nat := [1, 2, 1, 1, 5, 2, 1, 4, 2, 1, 3]
def baseStart_7934857 : Nat := 118140960795 + 7934857 * 2 ^ 59
def prefixEnd_7934857 : Nat := 4983230072969 + 3 ^ 40 * 7934857 * 2
def baseEnd_7934857 : Nat := 4074395565692966569195763

theorem tailTrace_7934857 : CollatzResearch.WordTrace tailWord_7934857 prefixEnd_7934857 4074395565692966569195763 := by
  unfold tailWord_7934857
  simp only [CollatzResearch.WordTrace]
  refine ⟨289408010614375729530458825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192938673742917153020305883 289408010614375729530458825)
  ·
    refine ⟨217056007960781797147844119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289408010614375729530458825 217056007960781797147844119)
    ·
      refine ⟨325584011941172695721766179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217056007960781797147844119 325584011941172695721766179)
      ·
        refine ⟨488376017911759043582649269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325584011941172695721766179 488376017911759043582649269)
        ·
          refine ⟨45785251679227410335873369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 488376017911759043582649269 45785251679227410335873369)
          ·
            refine ⟨34338938759420557751905027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45785251679227410335873369 34338938759420557751905027)
            ·
              refine ⟨51508408139130836627857541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34338938759420557751905027 51508408139130836627857541)
              ·
                refine ⟨9657826526087031867723289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51508408139130836627857541 9657826526087031867723289)
                ·
                  refine ⟨7243369894565273900792467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9657826526087031867723289 7243369894565273900792467)
                  ·
                    refine ⟨10865054841847910851188701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7243369894565273900792467 10865054841847910851188701)
                    ·
                      refine ⟨4074395565692966569195763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10865054841847910851188701 4074395565692966569195763)
                      ·
                        rfl

theorem cell23_7934857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 1, 3].length) (baseStart_7934857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934857 prefixEnd_7934857 := by exact prefixLift 7934857
  have htrace : WordTrace (prefixWord ++ tailWord_7934857) baseStart_7934857 baseEnd_7934857 := by
    simpa [prefixWord, tailWord_7934857, baseEnd_7934857] using wordTrace_append hprefix tailTrace_7934857
  have hstable : (prefixWord ++ tailWord_7934857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934857).length < 2 ^ (prefixWord ++ tailWord_7934857).sum := by decide
  have hdescent : baseEnd_7934857 < baseStart_7934857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934858 : List Nat := [3, 1, 2, 4, 1, 1, 4, 2, 1, 2, 2]
def baseStart_7934858 : Nat := 118140960795 + 7934858 * 2 ^ 59
def prefixEnd_7934858 : Nat := 4983230072969 + 3 ^ 40 * 7934858 * 2
def baseEnd_7934858 : Nat := 4074396079173621065283259

theorem tailTrace_7934858 : CollatzResearch.WordTrace tailWord_7934858 prefixEnd_7934858 4074396079173621065283259 := by
  unfold tailWord_7934858
  simp only [CollatzResearch.WordTrace]
  refine ⟨72352011771843026675311307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192938698058248071134163485 72352011771843026675311307)
  ·
    refine ⟨108528017657764540012966961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72352011771843026675311307 108528017657764540012966961)
    ·
      refine ⟨81396013243323405009725221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108528017657764540012966961 81396013243323405009725221)
      ·
        refine ⟨15261752483123138439323479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81396013243323405009725221 15261752483123138439323479)
        ·
          refine ⟨22892628724684707658985219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15261752483123138439323479 22892628724684707658985219)
          ·
            refine ⟨34338943087027061488477829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22892628724684707658985219 34338943087027061488477829)
            ·
              refine ⟨6438551828817574029089593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34338943087027061488477829 6438551828817574029089593)
              ·
                refine ⟨4828913871613180521817195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6438551828817574029089593 4828913871613180521817195)
                ·
                  refine ⟨7243370807419770782725793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4828913871613180521817195 7243370807419770782725793)
                  ·
                    refine ⟨5432528105564828087044345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7243370807419770782725793 5432528105564828087044345)
                    ·
                      refine ⟨4074396079173621065283259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5432528105564828087044345 4074396079173621065283259)
                      ·
                        rfl

theorem cell23_7934858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_7934858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934858 prefixEnd_7934858 := by exact prefixLift 7934858
  have htrace : WordTrace (prefixWord ++ tailWord_7934858) baseStart_7934858 baseEnd_7934858 := by
    simpa [prefixWord, tailWord_7934858, baseEnd_7934858] using wordTrace_append hprefix tailTrace_7934858
  have hstable : (prefixWord ++ tailWord_7934858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934858).length < 2 ^ (prefixWord ++ tailWord_7934858).sum := by decide
  have hdescent : baseEnd_7934858 < baseStart_7934858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934883 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 5]
def baseStart_7934883 : Nat := 118140960795 + 7934883 * 2 ^ 59
def prefixEnd_7934883 : Nat := 4983230072969 + 3 ^ 40 * 7934883 * 2
def baseEnd_7934883 : Nat := 4074408916189983467470643

theorem tailTrace_7934883 : CollatzResearch.WordTrace tailWord_7934883 prefixEnd_7934883 4074408916189983467470643 := by
  unfold tailWord_7934883
  simp only [CollatzResearch.WordTrace]
  refine ⟨289408958912281535970905303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192939305941521023980603535 289408958912281535970905303)
  ·
    refine ⟨434113438368422303956357955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289408958912281535970905303 434113438368422303956357955)
    ·
      refine ⟨651170157552633455934536933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434113438368422303956357955 651170157552633455934536933)
      ·
        refine ⟨122094404541118772987725675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 651170157552633455934536933 122094404541118772987725675)
        ·
          refine ⟨183141606811678159481588513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122094404541118772987725675 183141606811678159481588513)
          ·
            refine ⟨137356205108758619611191385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183141606811678159481588513 137356205108758619611191385)
            ·
              refine ⟨103017153831568964708393539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137356205108758619611191385 103017153831568964708393539)
              ·
                refine ⟨154525730747353447062590309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103017153831568964708393539 154525730747353447062590309)
                ·
                  refine ⟨28973574515128771324235683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154525730747353447062590309 28973574515128771324235683)
                  ·
                    refine ⟨43460361772693156986353525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28973574515128771324235683 43460361772693156986353525)
                    ·
                      refine ⟨4074408916189983467470643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43460361772693156986353525 4074408916189983467470643)
                      ·
                        rfl

theorem cell23_7934883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_7934883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934883 prefixEnd_7934883 := by exact prefixLift 7934883
  have htrace : WordTrace (prefixWord ++ tailWord_7934883) baseStart_7934883 baseEnd_7934883 := by
    simpa [prefixWord, tailWord_7934883, baseEnd_7934883] using wordTrace_append hprefix tailTrace_7934883
  have hstable : (prefixWord ++ tailWord_7934883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934883).length < 2 ^ (prefixWord ++ tailWord_7934883).sum := by decide
  have hdescent : baseEnd_7934883 < baseStart_7934883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934910 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_7934910 : Nat := 118140960795 + 7934910 * 2 ^ 59
def prefixEnd_7934910 : Nat := 4983230072969 + 3 ^ 40 * 7934910 * 2
def baseEnd_7934910 : Nat := 4074422780167654861833019

theorem tailTrace_7934910 : CollatzResearch.WordTrace tailWord_7934910 prefixEnd_7934910 4074422780167654861833019 := by
  unfold tailWord_7934910
  simp only [CollatzResearch.WordTrace]
  refine ⟨36176242960397964947767273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192939962455455813054758789 36176242960397964947767273)
  ·
    refine ⟨27132182220298473710825455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36176242960397964947767273 27132182220298473710825455)
    ·
      refine ⟨40698273330447710566238183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27132182220298473710825455 40698273330447710566238183)
      ·
        refine ⟨61047409995671565849357275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40698273330447710566238183 61047409995671565849357275)
        ·
          refine ⟨91571114993507348774035913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61047409995671565849357275 91571114993507348774035913)
          ·
            refine ⟨68678336245130511580526935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91571114993507348774035913 68678336245130511580526935)
            ·
              refine ⟨103017504367695767370790403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68678336245130511580526935 103017504367695767370790403)
              ·
                refine ⟨154526256551543651056185605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103017504367695767370790403 154526256551543651056185605)
                ·
                  refine ⟨28973673103414434573034801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154526256551543651056185605 28973673103414434573034801)
                  ·
                    refine ⟨21730254827560825929776101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28973673103414434573034801 21730254827560825929776101)
                    ·
                      refine ⟨4074422780167654861833019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21730254827560825929776101 4074422780167654861833019)
                      ·
                        rfl

theorem cell23_7934910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_7934910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934910 prefixEnd_7934910 := by exact prefixLift 7934910
  have htrace : WordTrace (prefixWord ++ tailWord_7934910) baseStart_7934910 baseEnd_7934910 := by
    simpa [prefixWord, tailWord_7934910, baseEnd_7934910] using wordTrace_append hprefix tailTrace_7934910
  have hstable : (prefixWord ++ tailWord_7934910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934910).length < 2 ^ (prefixWord ++ tailWord_7934910).sum := by decide
  have hdescent : baseEnd_7934910 < baseStart_7934910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934925 : List Nat := [1, 6, 3, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_7934925 : Nat := 118140960795 + 7934925 * 2 ^ 59
def prefixEnd_7934925 : Nat := 4983230072969 + 3 ^ 40 * 7934925 * 2
def baseEnd_7934925 : Nat := 4074430482377472303145451

theorem tailTrace_7934925 : CollatzResearch.WordTrace tailWord_7934925 prefixEnd_7934925 4074430482377472303145451 := by
  unfold tailWord_7934925
  simp only [CollatzResearch.WordTrace]
  refine ⟨289410490778129377143934229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192940327185419584762622819 289410490778129377143934229)
  ·
    refine ⟨13566116755224814553621917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 289410490778129377143934229 13566116755224814553621917)
    ·
      refine ⟨5087293783209305457608219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13566116755224814553621917 5087293783209305457608219)
      ·
        refine ⟨7630940674813958186412329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5087293783209305457608219 7630940674813958186412329)
        ·
          refine ⟨5723205506110468639809247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7630940674813958186412329 5723205506110468639809247)
          ·
            refine ⟨8584808259165702959713871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5723205506110468639809247 8584808259165702959713871)
            ·
              refine ⟨12877212388748554439570807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8584808259165702959713871 12877212388748554439570807)
              ·
                refine ⟨19315818583122831659356211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12877212388748554439570807 19315818583122831659356211)
                ·
                  refine ⟨28973727874684247489034317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19315818583122831659356211 28973727874684247489034317)
                  ·
                    refine ⟨10865147953006592808387869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28973727874684247489034317 10865147953006592808387869)
                    ·
                      refine ⟨4074430482377472303145451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10865147953006592808387869 4074430482377472303145451)
                      ·
                        rfl

theorem cell23_7934925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_7934925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934925 prefixEnd_7934925 := by exact prefixLift 7934925
  have htrace : WordTrace (prefixWord ++ tailWord_7934925) baseStart_7934925 baseEnd_7934925 := by
    simpa [prefixWord, tailWord_7934925, baseEnd_7934925] using wordTrace_append hprefix tailTrace_7934925
  have hstable : (prefixWord ++ tailWord_7934925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934925).length < 2 ^ (prefixWord ++ tailWord_7934925).sum := by decide
  have hdescent : baseEnd_7934925 < baseStart_7934925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7934954 : List Nat := [3, 1, 3, 1, 2, 4, 1, 3, 5]
def baseStart_7934954 : Nat := 118140960795 + 7934954 * 2 ^ 59
def prefixEnd_7934954 : Nat := 4983230072969 + 3 ^ 40 * 7934954 * 2
def baseEnd_7934954 : Nat := 452716152590716965520313

theorem tailTrace_7934954 : CollatzResearch.WordTrace tailWord_7934954 prefixEnd_7934954 452716152590716965520313 := by
  unfold tailWord_7934954
  simp only [CollatzResearch.WordTrace]
  refine ⟨72352887123756078774184979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192941032330016210064493277 72352887123756078774184979)
  ·
    refine ⟨108529330685634118161277469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72352887123756078774184979 108529330685634118161277469)
    ·
      refine ⟨40698499007112794310479051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108529330685634118161277469 40698499007112794310479051)
      ·
        refine ⟨61047748510669191465718577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40698499007112794310479051 61047748510669191465718577)
        ·
          refine ⟨45785811383001893599288933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61047748510669191465718577 45785811383001893599288933)
          ·
            refine ⟨8584839634312855049866675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45785811383001893599288933 8584839634312855049866675)
            ·
              refine ⟨12877259451469282574800013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8584839634312855049866675 12877259451469282574800013)
              ·
                refine ⟨4828972294300980965550005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12877259451469282574800013 4828972294300980965550005)
                ·
                  refine ⟨452716152590716965520313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4828972294300980965550005 452716152590716965520313)
                  ·
                    rfl

theorem cell23_7934954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 5].length) (baseStart_7934954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7934954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7934954 prefixEnd_7934954 := by exact prefixLift 7934954
  have htrace : WordTrace (prefixWord ++ tailWord_7934954) baseStart_7934954 baseEnd_7934954 := by
    simpa [prefixWord, tailWord_7934954, baseEnd_7934954] using wordTrace_append hprefix tailTrace_7934954
  have hstable : (prefixWord ++ tailWord_7934954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7934954).length < 2 ^ (prefixWord ++ tailWord_7934954).sum := by decide
  have hdescent : baseEnd_7934954 < baseStart_7934954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7934954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935004 : List Nat := [2, 2, 3, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_7935004 : Nat := 118140960795 + 7935004 * 2 ^ 59
def prefixEnd_7935004 : Nat := 4983230072969 + 3 ^ 40 * 7935004 * 2
def baseEnd_7935004 : Nat := 4074471047349177494057587

theorem tailTrace_7935004 : CollatzResearch.WordTrace tailWord_7935004 prefixEnd_7935004 4074471047349177494057587 := by
  unfold tailWord_7935004
  simp only [CollatzResearch.WordTrace]
  refine ⟨144706686072421586818030033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192942248096562115757373377 144706686072421586818030033)
  ·
    refine ⟨108530014554316190113522525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144706686072421586818030033 108530014554316190113522525)
    ·
      refine ⟨40698755457868571292570947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108530014554316190113522525 40698755457868571292570947)
      ·
        refine ⟨61048133186802856938856421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40698755457868571292570947 61048133186802856938856421)
        ·
          refine ⟨11446524972525535676035579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61048133186802856938856421 11446524972525535676035579)
          ·
            refine ⟨17169787458788303514053369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11446524972525535676035579 17169787458788303514053369)
            ·
              refine ⟨12877340594091227635540027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17169787458788303514053369 12877340594091227635540027)
              ·
                refine ⟨19316010891136841453310041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12877340594091227635540027 19316010891136841453310041)
                ·
                  refine ⟨14487008168352631089982531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19316010891136841453310041 14487008168352631089982531)
                  ·
                    refine ⟨21730512252528946634973797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14487008168352631089982531 21730512252528946634973797)
                    ·
                      refine ⟨4074471047349177494057587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21730512252528946634973797 4074471047349177494057587)
                      ·
                        rfl

theorem cell23_7935004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_7935004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935004 prefixEnd_7935004 := by exact prefixLift 7935004
  have htrace : WordTrace (prefixWord ++ tailWord_7935004) baseStart_7935004 baseEnd_7935004 := by
    simpa [prefixWord, tailWord_7935004, baseEnd_7935004] using wordTrace_append hprefix tailTrace_7935004
  have hstable : (prefixWord ++ tailWord_7935004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935004).length < 2 ^ (prefixWord ++ tailWord_7935004).sum := by decide
  have hdescent : baseEnd_7935004 < baseStart_7935004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935007 : List Nat := [1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 3]
def baseStart_7935007 : Nat := 118140960795 + 7935007 * 2 ^ 59
def prefixEnd_7935007 : Nat := 4983230072969 + 3 ^ 40 * 7935007 * 2
def baseEnd_7935007 : Nat := 4074472587791140982320073

theorem tailTrace_7935007 : CollatzResearch.WordTrace tailWord_7935007 prefixEnd_7935007 4074472587791140982320073 := by
  unfold tailWord_7935007
  simp only [CollatzResearch.WordTrace]
  refine ⟨289413481563832305148419275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192942321042554870098946183 289413481563832305148419275)
  ·
    refine ⟨434120222345748457722628913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289413481563832305148419275 434120222345748457722628913)
    ·
      refine ⟨325590166759311343291971685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434120222345748457722628913 325590166759311343291971685)
      ·
        refine ⟨61048156267370876867244691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325590166759311343291971685 61048156267370876867244691)
        ·
          refine ⟨91572234401056315300867037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61048156267370876867244691 91572234401056315300867037)
          ·
            refine ⟨34339587900396118237825139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91572234401056315300867037 34339587900396118237825139)
            ·
              refine ⟨51509381850594177356737709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34339587900396118237825139 51509381850594177356737709)
              ·
                refine ⟨19316018193972816508776641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51509381850594177356737709 19316018193972816508776641)
                ·
                  refine ⟨14487013645479612381582481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19316018193972816508776641 14487013645479612381582481)
                  ·
                    refine ⟨10865260234109709286186861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14487013645479612381582481 10865260234109709286186861)
                    ·
                      refine ⟨4074472587791140982320073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10865260234109709286186861 4074472587791140982320073)
                      ·
                        rfl

theorem cell23_7935007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_7935007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935007 prefixEnd_7935007 := by exact prefixLift 7935007
  have htrace : WordTrace (prefixWord ++ tailWord_7935007) baseStart_7935007 baseEnd_7935007 := by
    simpa [prefixWord, tailWord_7935007, baseEnd_7935007] using wordTrace_append hprefix tailTrace_7935007
  have hstable : (prefixWord ++ tailWord_7935007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935007).length < 2 ^ (prefixWord ++ tailWord_7935007).sum := by decide
  have hdescent : baseEnd_7935007 < baseStart_7935007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935040 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 5, 5]
def baseStart_7935040 : Nat := 118140960795 + 7935040 * 2 ^ 59
def prefixEnd_7935040 : Nat := 4983230072969 + 3 ^ 40 * 7935040 * 2
def baseEnd_7935040 : Nat := 1358163177550913117735807

theorem tailTrace_7935040 : CollatzResearch.WordTrace tailWord_7935040 prefixEnd_7935040 1358163177550913117735807 := by
  unfold tailWord_7935040
  simp only [CollatzResearch.WordTrace]
  refine ⟨144707342586356375892185287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192943123448475167856247049 144707342586356375892185287)
  ·
    refine ⟨217061013879534563838277931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144707342586356375892185287 217061013879534563838277931)
    ·
      refine ⟨325591520819301845757416897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217061013879534563838277931 325591520819301845757416897)
      ·
        refine ⟨244193640614476384318062673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325591520819301845757416897 244193640614476384318062673)
        ·
          refine ⟨183145230460857288238547005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244193640614476384318062673 183145230460857288238547005)
          ·
            refine ⟨68679461422821483089455127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183145230460857288238547005 68679461422821483089455127)
            ·
              refine ⟨103019192134232224634182691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68679461422821483089455127 103019192134232224634182691)
              ·
                refine ⟨154528788201348336951274037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103019192134232224634182691 154528788201348336951274037)
                ·
                  refine ⟨14487073893876406589181941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154528788201348336951274037 14487073893876406589181941)
                  ·
                    refine ⟨1358163177550913117735807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14487073893876406589181941 1358163177550913117735807)
                    ·
                      rfl

theorem cell23_7935040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 5, 5].length) (baseStart_7935040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935040 prefixEnd_7935040 := by exact prefixLift 7935040
  have htrace : WordTrace (prefixWord ++ tailWord_7935040) baseStart_7935040 baseEnd_7935040 := by
    simpa [prefixWord, tailWord_7935040, baseEnd_7935040] using wordTrace_append hprefix tailTrace_7935040
  have hstable : (prefixWord ++ tailWord_7935040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935040).length < 2 ^ (prefixWord ++ tailWord_7935040).sum := by decide
  have hdescent : baseEnd_7935040 < baseStart_7935040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935054 : List Nat := [4, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3]
def baseStart_7935054 : Nat := 118140960795 + 7935054 * 2 ^ 59
def prefixEnd_7935054 : Nat := 4983230072969 + 3 ^ 40 * 7935054 * 2
def baseEnd_7935054 : Nat := 4074496721381902298432357

theorem tailTrace_7935054 : CollatzResearch.WordTrace tailWord_7935054 prefixEnd_7935054 4074496721381902298432357 := by
  unfold tailWord_7935054
  simp only [CollatzResearch.WordTrace]
  refine ⟨36176899474332754021922527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192943463863108021450253477 36176899474332754021922527)
  ·
    refine ⟨54265349211499131032883791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36176899474332754021922527 54265349211499131032883791)
    ·
      refine ⟨81398023817248696549325687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54265349211499131032883791 81398023817248696549325687)
      ·
        refine ⟨122097035725873044823988531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81398023817248696549325687 122097035725873044823988531)
        ·
          refine ⟨183145553588809567235982797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122097035725873044823988531 183145553588809567235982797)
          ·
            refine ⟨68679582595803587713493549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183145553588809567235982797 68679582595803587713493549)
            ·
              refine ⟨25754843473426345392560081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68679582595803587713493549 25754843473426345392560081)
              ·
                refine ⟨19316132605069759044420061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25754843473426345392560081 19316132605069759044420061)
                ·
                  refine ⟨7243549726901159641657523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19316132605069759044420061 7243549726901159641657523)
                  ·
                    refine ⟨10865324590351739462486285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7243549726901159641657523 10865324590351739462486285)
                    ·
                      refine ⟨4074496721381902298432357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10865324590351739462486285 4074496721381902298432357)
                      ·
                        rfl

theorem cell23_7935054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_7935054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935054 prefixEnd_7935054 := by exact prefixLift 7935054
  have htrace : WordTrace (prefixWord ++ tailWord_7935054) baseStart_7935054 baseEnd_7935054 := by
    simpa [prefixWord, tailWord_7935054, baseEnd_7935054] using wordTrace_append hprefix tailTrace_7935054
  have hstable : (prefixWord ++ tailWord_7935054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935054).length < 2 ^ (prefixWord ++ tailWord_7935054).sum := by decide
  have hdescent : baseEnd_7935054 < baseStart_7935054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935071 : List Nat := [1, 1, 2, 3, 1, 1, 6, 3, 1, 1, 3]
def baseStart_7935071 : Nat := 118140960795 + 7935071 * 2 ^ 59
def prefixEnd_7935071 : Nat := 4983230072969 + 3 ^ 40 * 7935071 * 2
def baseEnd_7935071 : Nat := 4074505450553028731919779

theorem tailTrace_7935071 : CollatzResearch.WordTrace tailWord_7935071 prefixEnd_7935071 4074505450553028731919779 := by
  unfold tailWord_7935071
  simp only [CollatzResearch.WordTrace]
  refine ⟨289415815835600444078749067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192943877223733629385832711 289415815835600444078749067)
  ·
    refine ⟨434123723753400666118123601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289415815835600444078749067 434123723753400666118123601)
    ·
      refine ⟨325592792815050499588592701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434123723753400666118123601 325592792815050499588592701)
      ·
        refine ⟨122097297305643937345722263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325592792815050499588592701 122097297305643937345722263)
        ·
          refine ⟨183145945958465906018583395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122097297305643937345722263 183145945958465906018583395)
          ·
            refine ⟨274718918937698859027875093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183145945958465906018583395 274718918937698859027875093)
            ·
              refine ⟨12877449325204634016931645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 274718918937698859027875093 12877449325204634016931645)
              ·
                refine ⟨4829043496951737756349367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12877449325204634016931645 4829043496951737756349367)
                ·
                  refine ⟨7243565245427606634524051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4829043496951737756349367 7243565245427606634524051)
                  ·
                    refine ⟨10865347868141409951786077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7243565245427606634524051 10865347868141409951786077)
                    ·
                      refine ⟨4074505450553028731919779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10865347868141409951786077 4074505450553028731919779)
                      ·
                        rfl

theorem cell23_7935071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_7935071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935071 prefixEnd_7935071 := by exact prefixLift 7935071
  have htrace : WordTrace (prefixWord ++ tailWord_7935071) baseStart_7935071 baseEnd_7935071 := by
    simpa [prefixWord, tailWord_7935071, baseEnd_7935071] using wordTrace_append hprefix tailTrace_7935071
  have hstable : (prefixWord ++ tailWord_7935071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935071).length < 2 ^ (prefixWord ++ tailWord_7935071).sum := by decide
  have hdescent : baseEnd_7935071 < baseStart_7935071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935087 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 4, 4]
def baseStart_7935087 : Nat := 118140960795 + 7935087 * 2 ^ 59
def prefixEnd_7935087 : Nat := 4983230072969 + 3 ^ 40 * 7935087 * 2
def baseEnd_7935087 : Nat := 1358171222081166889773235

theorem tailTrace_7935087 : CollatzResearch.WordTrace tailWord_7935087 prefixEnd_7935087 1358171222081166889773235 := by
  unfold tailWord_7935087
  simp only [CollatzResearch.WordTrace]
  refine ⟨289416399403542478811331515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192944266269028319207554343 289416399403542478811331515)
  ·
    refine ⟨434124599105313718216997273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289416399403542478811331515 434124599105313718216997273)
    ·
      refine ⟨325593449328985288662747955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434124599105313718216997273 325593449328985288662747955)
      ·
        refine ⟨488390173993477932994121933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325593449328985288662747955 488390173993477932994121933)
        ·
          refine ⟨183146315247554224872795725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 488390173993477932994121933 183146315247554224872795725)
          ·
            refine ⟨68679868217832834327298397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183146315247554224872795725 68679868217832834327298397)
            ·
              refine ⟨25754950581687312872736899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68679868217832834327298397 25754950581687312872736899)
              ·
                refine ⟨38632425872530969309105349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25754950581687312872736899 38632425872530969309105349)
                ·
                  refine ⟨7243579851099556745457253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38632425872530969309105349 7243579851099556745457253)
                  ·
                    refine ⟨1358171222081166889773235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7243579851099556745457253 1358171222081166889773235)
                    ·
                      rfl

theorem cell23_7935087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 4].length) (baseStart_7935087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935087 prefixEnd_7935087 := by exact prefixLift 7935087
  have htrace : WordTrace (prefixWord ++ tailWord_7935087) baseStart_7935087 baseEnd_7935087 := by
    simpa [prefixWord, tailWord_7935087, baseEnd_7935087] using wordTrace_append hprefix tailTrace_7935087
  have hstable : (prefixWord ++ tailWord_7935087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935087).length < 2 ^ (prefixWord ++ tailWord_7935087).sum := by decide
  have hdescent : baseEnd_7935087 < baseStart_7935087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935100 : List Nat := [2, 2, 2, 1, 1, 3, 2, 10]
def baseStart_7935100 : Nat := 118140960795 + 7935100 * 2 ^ 59
def prefixEnd_7935100 : Nat := 4983230072969 + 3 ^ 40 * 7935100 * 2
def baseEnd_7935100 : Nat := 150908160796000337720635

theorem tailTrace_7935100 : CollatzResearch.WordTrace tailWord_7935100 prefixEnd_7935100 150908160796000337720635 := by
  unfold tailWord_7935100
  simp only [CollatzResearch.WordTrace]
  refine ⟨144708436776247691015777377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192944582368330254687703169 144708436776247691015777377)
  ·
    refine ⟨108531327582185768261833033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144708436776247691015777377 108531327582185768261833033)
    ·
      refine ⟨81398495686639326196374775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108531327582185768261833033 81398495686639326196374775)
      ·
        refine ⟨122097743529958989294562163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81398495686639326196374775 122097743529958989294562163)
        ·
          refine ⟨183146615294938483941843245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122097743529958989294562163 183146615294938483941843245)
          ·
            refine ⟨68679980735601931478191217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183146615294938483941843245 68679980735601931478191217)
            ·
              refine ⟨51509985551701448608643413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68679980735601931478191217 51509985551701448608643413)
              ·
                refine ⟨150908160796000337720635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51509985551701448608643413 150908160796000337720635)
                ·
                  rfl

theorem cell23_7935100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 10].length) (baseStart_7935100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935100 prefixEnd_7935100 := by exact prefixLift 7935100
  have htrace : WordTrace (prefixWord ++ tailWord_7935100) baseStart_7935100 baseEnd_7935100 := by
    simpa [prefixWord, tailWord_7935100, baseEnd_7935100] using wordTrace_append hprefix tailTrace_7935100
  have hstable : (prefixWord ++ tailWord_7935100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935100).length < 2 ^ (prefixWord ++ tailWord_7935100).sum := by decide
  have hdescent : baseEnd_7935100 < baseStart_7935100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935134 : List Nat := [4, 3, 1, 1, 2, 3, 9]
def baseStart_7935134 : Nat := 118140960795 + 7935134 * 2 ^ 59
def prefixEnd_7935134 : Nat := 4983230072969 + 3 ^ 40 * 7935134 * 2
def baseEnd_7935134 : Nat := 50302935800422987474469

theorem tailTrace_7935134 : CollatzResearch.WordTrace tailWord_7935134 prefixEnd_7935134 50302935800422987474469 := by
  unfold tailWord_7935134
  simp only [CollatzResearch.WordTrace]
  refine ⟨36177264204296525729786557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192945409089581470558861637 36177264204296525729786557)
  ·
    refine ⟨13566474076611197148669959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36177264204296525729786557 13566474076611197148669959)
    ·
      refine ⟨20349711114916795723004939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13566474076611197148669959 20349711114916795723004939)
      ·
        refine ⟨30524566672375193584507409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20349711114916795723004939 30524566672375193584507409)
        ·
          refine ⟨22893425004281395188380557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30524566672375193584507409 22893425004281395188380557)
          ·
            refine ⟨8585034376605523195642709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22893425004281395188380557 8585034376605523195642709)
            ·
              refine ⟨50302935800422987474469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8585034376605523195642709 50302935800422987474469)
              ·
                rfl

theorem cell23_7935134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 9].length) (baseStart_7935134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935134 prefixEnd_7935134 := by exact prefixLift 7935134
  have htrace : WordTrace (prefixWord ++ tailWord_7935134) baseStart_7935134 baseEnd_7935134 := by
    simpa [prefixWord, tailWord_7935134, baseEnd_7935134] using wordTrace_append hprefix tailTrace_7935134
  have hstable : (prefixWord ++ tailWord_7935134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935134).length < 2 ^ (prefixWord ++ tailWord_7935134).sum := by decide
  have hdescent : baseEnd_7935134 < baseStart_7935134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935161 : List Nat := [1, 2, 1, 4, 1, 4, 1, 3, 2, 1, 3]
def baseStart_7935161 : Nat := 118140960795 + 7935161 * 2 ^ 59
def prefixEnd_7935161 : Nat := 4983230072969 + 3 ^ 40 * 7935161 * 2
def baseEnd_7935161 : Nat := 4074551663811933379794365

theorem tailTrace_7935161 : CollatzResearch.WordTrace tailWord_7935161 prefixEnd_7935161 4074551663811933379794365 := by
  unfold tailWord_7935161
  simp only [CollatzResearch.WordTrace]
  refine ⟨289419098405274389449525337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192946065603516259633016891 289419098405274389449525337)
  ·
    refine ⟨217064323803955792087144003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289419098405274389449525337 217064323803955792087144003)
    ·
      refine ⟨325596485705933688130716005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217064323803955792087144003 325596485705933688130716005)
      ·
        refine ⟨61049341069862566524509251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325596485705933688130716005 61049341069862566524509251)
        ·
          refine ⟨91574011604793849786763877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61049341069862566524509251 91574011604793849786763877)
          ·
            refine ⟨17170127175898846835018227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91574011604793849786763877 17170127175898846835018227)
            ·
              refine ⟨25755190763848270252527341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17170127175898846835018227 25755190763848270252527341)
              ·
                refine ⟨9658196536443101344697753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25755190763848270252527341 9658196536443101344697753)
                ·
                  refine ⟨7243647402332326008523315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9658196536443101344697753 7243647402332326008523315)
                  ·
                    refine ⟨10865471103498489012784973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7243647402332326008523315 10865471103498489012784973)
                    ·
                      refine ⟨4074551663811933379794365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10865471103498489012784973 4074551663811933379794365)
                      ·
                        rfl

theorem cell23_7935161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_7935161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935161 prefixEnd_7935161 := by exact prefixLift 7935161
  have htrace : WordTrace (prefixWord ++ tailWord_7935161) baseStart_7935161 baseEnd_7935161 := by
    simpa [prefixWord, tailWord_7935161, baseEnd_7935161] using wordTrace_append hprefix tailTrace_7935161
  have hstable : (prefixWord ++ tailWord_7935161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935161).length < 2 ^ (prefixWord ++ tailWord_7935161).sum := by decide
  have hdescent : baseEnd_7935161 < baseStart_7935161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935218 : List Nat := [3, 2, 1, 3, 3, 1, 2, 1, 1, 4, 2]
def baseStart_7935218 : Nat := 118140960795 + 7935218 * 2 ^ 59
def prefixEnd_7935218 : Nat := 4983230072969 + 3 ^ 40 * 7935218 * 2
def baseEnd_7935218 : Nat := 4074580932209239656781603

theorem tailTrace_7935218 : CollatzResearch.WordTrace tailWord_7935218 prefixEnd_7935218 4074580932209239656781603 := by
  unfold tailWord_7935218
  simp only [CollatzResearch.WordTrace]
  refine ⟨72355294341516972046087577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192947451577378592122900205 72355294341516972046087577)
  ·
    refine ⟨54266470756137729034565683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72355294341516972046087577 54266470756137729034565683)
    ·
      refine ⟨81399706134206593551848525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54266470756137729034565683 81399706134206593551848525)
      ·
        refine ⟨30524889800327472581943197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81399706134206593551848525 30524889800327472581943197)
        ·
          refine ⟨11446833675122802218228699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30524889800327472581943197 11446833675122802218228699)
          ·
            refine ⟨17170250512684203327343049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11446833675122802218228699 17170250512684203327343049)
            ·
              refine ⟨12877687884513152495507287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17170250512684203327343049 12877687884513152495507287)
              ·
                refine ⟨19316531826769728743260931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12877687884513152495507287 19316531826769728743260931)
                ·
                  refine ⟨28974797740154593114891397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19316531826769728743260931 28974797740154593114891397)
                  ·
                    refine ⟨5432774576278986209042137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28974797740154593114891397 5432774576278986209042137)
                    ·
                      refine ⟨4074580932209239656781603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5432774576278986209042137 4074580932209239656781603)
                      ·
                        rfl

theorem cell23_7935218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_7935218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935218 prefixEnd_7935218 := by exact prefixLift 7935218
  have htrace : WordTrace (prefixWord ++ tailWord_7935218) baseStart_7935218 baseEnd_7935218 := by
    simpa [prefixWord, tailWord_7935218, baseEnd_7935218] using wordTrace_append hprefix tailTrace_7935218
  have hstable : (prefixWord ++ tailWord_7935218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935218).length < 2 ^ (prefixWord ++ tailWord_7935218).sum := by decide
  have hdescent : baseEnd_7935218 < baseStart_7935218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935237 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 1, 7]
def baseStart_7935237 : Nat := 118140960795 + 7935237 * 2 ^ 59
def prefixEnd_7935237 : Nat := 4983230072969 + 3 ^ 40 * 7935237 * 2
def baseEnd_7935237 : Nat := 1358196896113891694148005

theorem tailTrace_7935237 : CollatzResearch.WordTrace tailWord_7935237 prefixEnd_7935237 1358196896113891694148005 := by
  unfold tailWord_7935237
  simp only [CollatzResearch.WordTrace]
  refine ⟨289421870352999054429291965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192947913568666036286194643 289421870352999054429291965)
  ·
    refine ⟨108533201382374645410984487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289421870352999054429291965 108533201382374645410984487)
    ·
      refine ⟨162799802073561968116476731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108533201382374645410984487 162799802073561968116476731)
      ·
        refine ⟨244199703110342952174715097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162799802073561968116476731 244199703110342952174715097)
        ·
          refine ⟨183149777332757214131036323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244199703110342952174715097 183149777332757214131036323)
          ·
            refine ⟨274724665999135821196554485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183149777332757214131036323 274724665999135821196554485)
            ·
              refine ⟨25755437437418983237176983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274724665999135821196554485 25755437437418983237176983)
              ·
                refine ⟨38633156156128474855765475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25755437437418983237176983 38633156156128474855765475)
                ·
                  refine ⟨57949734234192712283648213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38633156156128474855765475 57949734234192712283648213)
                  ·
                    refine ⟨1358196896113891694148005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57949734234192712283648213 1358196896113891694148005)
                    ·
                      rfl

theorem cell23_7935237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_7935237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935237 prefixEnd_7935237 := by exact prefixLift 7935237
  have htrace : WordTrace (prefixWord ++ tailWord_7935237) baseStart_7935237 baseEnd_7935237 := by
    simpa [prefixWord, tailWord_7935237, baseEnd_7935237] using wordTrace_append hprefix tailTrace_7935237
  have hstable : (prefixWord ++ tailWord_7935237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935237).length < 2 ^ (prefixWord ++ tailWord_7935237).sum := by decide
  have hdescent : baseEnd_7935237 < baseStart_7935237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935284 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_7935284 : Nat := 118140960795 + 7935284 * 2 ^ 59
def prefixEnd_7935284 : Nat := 4983230072969 + 3 ^ 40 * 7935284 * 2
def baseEnd_7935284 : Nat := 1358204940644145466185433

theorem tailTrace_7935284 : CollatzResearch.WordTrace tailWord_7935284 prefixEnd_7935284 1358204940644145466185433 := by
  unfold tailWord_7935284
  simp only [CollatzResearch.WordTrace]
  refine ⟨144711792291914390728126453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192949056389219187637501937 144711792291914390728126453)
  ·
    refine ⟨13566730527366974130761855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144711792291914390728126453 13566730527366974130761855)
    ·
      refine ⟨20350095791050461196142783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13566730527366974130761855 20350095791050461196142783)
      ·
        refine ⟨30525143686575691794214175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20350095791050461196142783 30525143686575691794214175)
        ·
          refine ⟨45787715529863537691321263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30525143686575691794214175 45787715529863537691321263)
          ·
            refine ⟨68681573294795306536981895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45787715529863537691321263 68681573294795306536981895)
            ·
              refine ⟨103022359942192959805472843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68681573294795306536981895 103022359942192959805472843)
              ·
                refine ⟨154533539913289439708209265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103022359942192959805472843 154533539913289439708209265)
                ·
                  refine ⟨115900154934967079781156949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154533539913289439708209265 115900154934967079781156949)
                  ·
                    refine ⟨1358204940644145466185433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115900154934967079781156949 1358204940644145466185433)
                    ·
                      rfl

theorem cell23_7935284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_7935284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935284 prefixEnd_7935284 := by exact prefixLift 7935284
  have htrace : WordTrace (prefixWord ++ tailWord_7935284) baseStart_7935284 baseEnd_7935284 := by
    simpa [prefixWord, tailWord_7935284, baseEnd_7935284] using wordTrace_append hprefix tailTrace_7935284
  have hstable : (prefixWord ++ tailWord_7935284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935284).length < 2 ^ (prefixWord ++ tailWord_7935284).sum := by decide
  have hdescent : baseEnd_7935284 < baseStart_7935284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935314 : List Nat := [3, 2, 2, 1, 1, 1, 1, 6, 6]
def baseStart_7935314 : Nat := 118140960795 + 7935314 * 2 ^ 59
def prefixEnd_7935314 : Nat := 4983230072969 + 3 ^ 40 * 7935314 * 2
def baseEnd_7935314 : Nat := 452736691816896809020129

theorem tailTrace_7935314 : CollatzResearch.WordTrace tailWord_7935314 prefixEnd_7935314 452736691816896809020129 := by
  unfold tailWord_7935314
  simp only [CollatzResearch.WordTrace]
  refine ⟨72356169693430024144961249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192949785849146731053229997 72356169693430024144961249)
  ·
    refine ⟨54267127270072518108720937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72356169693430024144961249 54267127270072518108720937)
    ·
      refine ⟨40700345452554388581540703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54267127270072518108720937 40700345452554388581540703)
      ·
        refine ⟨61050518178831582872311055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40700345452554388581540703 61050518178831582872311055)
        ·
          refine ⟨91575777268247374308466583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61050518178831582872311055 91575777268247374308466583)
          ·
            refine ⟨137363665902371061462699875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91575777268247374308466583 137363665902371061462699875)
            ·
              refine ⟨206045498853556592194049813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137363665902371061462699875 206045498853556592194049813)
              ·
                refine ⟨9658382758760465259096085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 206045498853556592194049813 9658382758760465259096085)
                ·
                  refine ⟨452736691816896809020129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9658382758760465259096085 452736691816896809020129)
                  ·
                    rfl

theorem cell23_7935314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_7935314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935314 prefixEnd_7935314 := by exact prefixLift 7935314
  have htrace : WordTrace (prefixWord ++ tailWord_7935314) baseStart_7935314 baseEnd_7935314 := by
    simpa [prefixWord, tailWord_7935314, baseEnd_7935314] using wordTrace_append hprefix tailTrace_7935314
  have hstable : (prefixWord ++ tailWord_7935314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935314).length < 2 ^ (prefixWord ++ tailWord_7935314).sum := by decide
  have hdescent : baseEnd_7935314 < baseStart_7935314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935327 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 2, 9]
def baseStart_7935327 : Nat := 118140960795 + 7935327 * 2 ^ 59
def prefixEnd_7935327 : Nat := 4983230072969 + 3 ^ 40 * 7935327 * 2
def baseEnd_7935327 : Nat := 1358212300533526576772867

theorem tailTrace_7935327 : CollatzResearch.WordTrace tailWord_7935327 prefixEnd_7935327 1358212300533526576772867 := by
  unfold tailWord_7935327
  simp only [CollatzResearch.WordTrace]
  refine ⟨289425152922672999800068235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192950101948448666533378823 289425152922672999800068235)
  ·
    refine ⟨434137729384009499700102353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289425152922672999800068235 434137729384009499700102353)
    ·
      refine ⟨325603297038007124775076765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434137729384009499700102353 325603297038007124775076765)
      ·
        refine ⟨122101236389252671790653787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325603297038007124775076765 122101236389252671790653787)
        ·
          refine ⟨183151854583879007685980681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122101236389252671790653787 183151854583879007685980681)
          ·
            refine ⟨137363890937909255764485511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183151854583879007685980681 137363890937909255764485511)
            ·
              refine ⟨206045836406863883646728267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137363890937909255764485511 206045836406863883646728267)
              ·
                refine ⟨309068754610295825470092401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206045836406863883646728267 309068754610295825470092401)
                ·
                  refine ⟨231801565957721869102569301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309068754610295825470092401 231801565957721869102569301)
                  ·
                    refine ⟨1358212300533526576772867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 231801565957721869102569301 1358212300533526576772867)
                    ·
                      rfl

theorem cell23_7935327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 9].length) (baseStart_7935327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935327 prefixEnd_7935327 := by exact prefixLift 7935327
  have htrace : WordTrace (prefixWord ++ tailWord_7935327) baseStart_7935327 baseEnd_7935327 := by
    simpa [prefixWord, tailWord_7935327, baseEnd_7935327] using wordTrace_append hprefix tailTrace_7935327
  have hstable : (prefixWord ++ tailWord_7935327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935327).length < 2 ^ (prefixWord ++ tailWord_7935327).sum := by decide
  have hdescent : baseEnd_7935327 < baseStart_7935327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935331 : List Nat := [1, 1, 1, 5, 2, 2, 4, 1, 6]
def baseStart_7935331 : Nat := 118140960795 + 7935331 * 2 ^ 59
def prefixEnd_7935331 : Nat := 4983230072969 + 3 ^ 40 * 7935331 * 2
def baseEnd_7935331 : Nat := 452737661724799746074287

theorem tailTrace_7935331 : CollatzResearch.WordTrace tailWord_7935331 prefixEnd_7935331 452737661724799746074287 := by
  unfold tailWord_7935331
  simp only [CollatzResearch.WordTrace]
  refine ⟨289425298814658508483213847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192950199209772338988809231 289425298814658508483213847)
  ·
    refine ⟨434137948221987762724820771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289425298814658508483213847 434137948221987762724820771)
    ·
      refine ⟨651206922332981644087231157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434137948221987762724820771 651206922332981644087231157)
      ·
        refine ⟨61050648968717029133177921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 651206922332981644087231157 61050648968717029133177921)
        ·
          refine ⟨45787986726537771849883441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61050648968717029133177921 45787986726537771849883441)
          ·
            refine ⟨34340990044903328887412581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45787986726537771849883441 34340990044903328887412581)
            ·
              refine ⟨6438935633419374166389859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34340990044903328887412581 6438935633419374166389859)
              ·
                refine ⟨9658403450129061249584789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6438935633419374166389859 9658403450129061249584789)
                ·
                  refine ⟨452737661724799746074287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9658403450129061249584789 452737661724799746074287)
                  ·
                    rfl

theorem cell23_7935331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 6].length) (baseStart_7935331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935331 prefixEnd_7935331 := by exact prefixLift 7935331
  have htrace : WordTrace (prefixWord ++ tailWord_7935331) baseStart_7935331 baseEnd_7935331 := by
    simpa [prefixWord, tailWord_7935331, baseEnd_7935331] using wordTrace_append hprefix tailTrace_7935331
  have hstable : (prefixWord ++ tailWord_7935331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935331).length < 2 ^ (prefixWord ++ tailWord_7935331).sum := by decide
  have hdescent : baseEnd_7935331 < baseStart_7935331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935337 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 7]
def baseStart_7935337 : Nat := 118140960795 + 7935337 * 2 ^ 59
def prefixEnd_7935337 : Nat := 4983230072969 + 3 ^ 40 * 7935337 * 2
def baseEnd_7935337 : Nat := 4074642036407124691193555

theorem tailTrace_7935337 : CollatzResearch.WordTrace tailWord_7935337 prefixEnd_7935337 4074642036407124691193555 := by
  unfold tailWord_7935337
  simp only [CollatzResearch.WordTrace]
  refine ⟨289425517652636771507932265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192950345101757847671954843 289425517652636771507932265)
  ·
    refine ⟨217069138239477578630949199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289425517652636771507932265 217069138239477578630949199)
    ·
      refine ⟨325603707359216367946423799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217069138239477578630949199 325603707359216367946423799)
      ·
        refine ⟨488405561038824551919635699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325603707359216367946423799 488405561038824551919635699)
        ·
          refine ⟨732608341558236827879453549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488405561038824551919635699 732608341558236827879453549)
          ·
            refine ⟨274728128084338810454795081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 732608341558236827879453549 274728128084338810454795081)
            ·
              refine ⟨206046096063254107841096311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274728128084338810454795081 206046096063254107841096311)
              ·
                refine ⟨309069144094881161761644467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206046096063254107841096311 309069144094881161761644467)
                ·
                  refine ⟨463603716142321742642466701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309069144094881161761644467 463603716142321742642466701)
                  ·
                    refine ⟨173851393553370653490925013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 463603716142321742642466701 173851393553370653490925013)
                    ·
                      refine ⟨4074642036407124691193555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173851393553370653490925013 4074642036407124691193555)
                      ·
                        rfl

theorem cell23_7935337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_7935337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935337 prefixEnd_7935337 := by exact prefixLift 7935337
  have htrace : WordTrace (prefixWord ++ tailWord_7935337) baseStart_7935337 baseEnd_7935337 := by
    simpa [prefixWord, tailWord_7935337, baseEnd_7935337] using wordTrace_append hprefix tailTrace_7935337
  have hstable : (prefixWord ++ tailWord_7935337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935337).length < 2 ^ (prefixWord ++ tailWord_7935337).sum := by decide
  have hdescent : baseEnd_7935337 < baseStart_7935337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935344 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 3, 5]
def baseStart_7935344 : Nat := 118140960795 + 7935344 * 2 ^ 59
def prefixEnd_7935344 : Nat := 4983230072969 + 3 ^ 40 * 7935344 * 2
def baseEnd_7935344 : Nat := 1358215210257235387935341

theorem tailTrace_7935344 : CollatzResearch.WordTrace tailWord_7935344 prefixEnd_7935344 1358215210257235387935341 := by
  unfold tailWord_7935344
  simp only [CollatzResearch.WordTrace]
  refine ⟨144712886481805705851718543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192950515309074274468958057 144712886481805705851718543)
  ·
    refine ⟨217069329722708558777577815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144712886481805705851718543 217069329722708558777577815)
    ·
      refine ⟨325603994584062838166366723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217069329722708558777577815 325603994584062838166366723)
      ·
        refine ⟨488405991876094257249550085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325603994584062838166366723 488405991876094257249550085)
        ·
          refine ⟨91576123476767673234290641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 488405991876094257249550085 91576123476767673234290641)
          ·
            refine ⟨68682092607575754925717981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91576123476767673234290641 68682092607575754925717981)
            ·
              refine ⟨25755784727840908097144243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68682092607575754925717981 25755784727840908097144243)
              ·
                refine ⟨38633677091761362145716365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25755784727840908097144243 38633677091761362145716365)
                ·
                  refine ⟨14487628909410510804643637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38633677091761362145716365 14487628909410510804643637)
                  ·
                    refine ⟨1358215210257235387935341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14487628909410510804643637 1358215210257235387935341)
                    ·
                      rfl

theorem cell23_7935344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 3, 5].length) (baseStart_7935344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935344 prefixEnd_7935344 := by exact prefixLift 7935344
  have htrace : WordTrace (prefixWord ++ tailWord_7935344) baseStart_7935344 baseEnd_7935344 := by
    simpa [prefixWord, tailWord_7935344, baseEnd_7935344] using wordTrace_append hprefix tailTrace_7935344
  have hstable : (prefixWord ++ tailWord_7935344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935344).length < 2 ^ (prefixWord ++ tailWord_7935344).sum := by decide
  have hdescent : baseEnd_7935344 < baseStart_7935344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935368 : List Nat := [2, 1, 3, 3, 1, 2, 2, 2, 2, 3, 2]
def baseStart_7935368 : Nat := 118140960795 + 7935368 * 2 ^ 59
def prefixEnd_7935368 : Nat := 4983230072969 + 3 ^ 40 * 7935368 * 2
def baseEnd_7935368 : Nat := 4074657954307414069905913

theorem tailTrace_7935368 : CollatzResearch.WordTrace tailWord_7935368 prefixEnd_7935368 4074657954307414069905913 := by
  unfold tailWord_7935368
  simp only [CollatzResearch.WordTrace]
  refine ⟨144713324157762231901155379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192951098877016309201540505 144713324157762231901155379)
  ·
    refine ⟨217069986236643347851733069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144713324157762231901155379 217069986236643347851733069)
    ·
      refine ⟨81401244838741255444399901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217069986236643347851733069 81401244838741255444399901)
      ·
        refine ⟨30525466814527970791649963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81401244838741255444399901 30525466814527970791649963)
        ·
          refine ⟨45788200221791956187474945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30525466814527970791649963 45788200221791956187474945)
          ·
            refine ⟨34341150166343967140606209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45788200221791956187474945 34341150166343967140606209)
            ·
              refine ⟨25755862624757975355454657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34341150166343967140606209 25755862624757975355454657)
              ·
                refine ⟨19316896968568481516590993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25755862624757975355454657 19316896968568481516590993)
                ·
                  refine ⟨14487672726426361137443245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19316896968568481516590993 14487672726426361137443245)
                  ·
                    refine ⟨5432877272409885426541217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14487672726426361137443245 5432877272409885426541217)
                    ·
                      refine ⟨4074657954307414069905913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5432877272409885426541217 4074657954307414069905913)
                      ·
                        rfl

theorem cell23_7935368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_7935368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935368 prefixEnd_7935368 := by exact prefixLift 7935368
  have htrace : WordTrace (prefixWord ++ tailWord_7935368) baseStart_7935368 baseEnd_7935368 := by
    simpa [prefixWord, tailWord_7935368, baseEnd_7935368] using wordTrace_append hprefix tailTrace_7935368
  have hstable : (prefixWord ++ tailWord_7935368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935368).length < 2 ^ (prefixWord ++ tailWord_7935368).sum := by decide
  have hdescent : baseEnd_7935368 < baseStart_7935368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935391 : List Nat := [1, 1, 2, 5, 1, 3, 2, 1, 1, 6]
def baseStart_7935391 : Nat := 118140960795 + 7935391 * 2 ^ 59
def prefixEnd_7935391 : Nat := 4983230072969 + 3 ^ 40 * 7935391 * 2
def baseEnd_7935391 : Nat := 1358223254787489159972769

theorem tailTrace_7935391 : CollatzResearch.WordTrace tailWord_7935391 prefixEnd_7935391 1358223254787489159972769 := by
  unfold tailWord_7935391
  simp only [CollatzResearch.WordTrace]
  refine ⟨289427487194441138730398027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192951658129627425820265351 289427487194441138730398027)
  ·
    refine ⟨434141230791661708095597041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289427487194441138730398027 434141230791661708095597041)
    ·
      refine ⟨325605923093746281071697781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434141230791661708095597041 325605923093746281071697781)
      ·
        refine ⟨30525555290038713850471667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325605923093746281071697781 30525555290038713850471667)
        ·
          refine ⟨45788332935058070775707501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30525555290038713850471667 45788332935058070775707501)
          ·
            refine ⟨17170624850646776540890313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45788332935058070775707501 17170624850646776540890313)
            ·
              refine ⟨12877968637985082405667735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17170624850646776540890313 12877968637985082405667735)
              ·
                refine ⟨19316952956977623608501603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12877968637985082405667735 19316952956977623608501603)
                ·
                  refine ⟨28975429435466435412752405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19316952956977623608501603 28975429435466435412752405)
                  ·
                    refine ⟨1358223254787489159972769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28975429435466435412752405 1358223254787489159972769)
                    ·
                      rfl

theorem cell23_7935391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 6].length) (baseStart_7935391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935391 prefixEnd_7935391 := by exact prefixLift 7935391
  have htrace : WordTrace (prefixWord ++ tailWord_7935391) baseStart_7935391 baseEnd_7935391 := by
    simpa [prefixWord, tailWord_7935391, baseEnd_7935391] using wordTrace_append hprefix tailTrace_7935391
  have hstable : (prefixWord ++ tailWord_7935391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935391).length < 2 ^ (prefixWord ++ tailWord_7935391).sum := by decide
  have hdescent : baseEnd_7935391 < baseStart_7935391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935426 : List Nat := [3, 5, 2, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_7935426 : Nat := 118140960795 + 7935426 * 2 ^ 59
def prefixEnd_7935426 : Nat := 4983230072969 + 3 ^ 40 * 7935426 * 2
def baseEnd_7935426 : Nat := 4074687736185374842980647

theorem tailTrace_7935426 : CollatzResearch.WordTrace tailWord_7935426 prefixEnd_7935426 4074687736185374842980647 := by
  unfold tailWord_7935426
  simp only [CollatzResearch.WordTrace]
  refine ⟨72357190937328584926980533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192952509166209559805281421 72357190937328584926980533)
  ·
    refine ⟨6783486650374554836904425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72357190937328584926980533 6783486650374554836904425)
    ·
      refine ⟨5087614987780916127678319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6783486650374554836904425 5087614987780916127678319)
      ·
        refine ⟨7631422481671374191517479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5087614987780916127678319 7631422481671374191517479)
        ·
          refine ⟨11447133722507061287276219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7631422481671374191517479 11447133722507061287276219)
          ·
            refine ⟨17170700583760591930914329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11447133722507061287276219 17170700583760591930914329)
            ·
              refine ⟨12878025437820443948185747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17170700583760591930914329 12878025437820443948185747)
              ·
                refine ⟨19317038156730665922278621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12878025437820443948185747 19317038156730665922278621)
                ·
                  refine ⟨7243889308773999720854483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19317038156730665922278621 7243889308773999720854483)
                  ·
                    refine ⟨10865833963160999581281725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7243889308773999720854483 10865833963160999581281725)
                    ·
                      refine ⟨4074687736185374842980647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10865833963160999581281725 4074687736185374842980647)
                      ·
                        rfl

theorem cell23_7935426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_7935426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935426 prefixEnd_7935426 := by exact prefixLift 7935426
  have htrace : WordTrace (prefixWord ++ tailWord_7935426) baseStart_7935426 baseEnd_7935426 := by
    simpa [prefixWord, tailWord_7935426, baseEnd_7935426] using wordTrace_append hprefix tailTrace_7935426
  have hstable : (prefixWord ++ tailWord_7935426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935426).length < 2 ^ (prefixWord ++ tailWord_7935426).sum := by decide
  have hdescent : baseEnd_7935426 < baseStart_7935426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935448 : List Nat := [2, 1, 2, 2, 2, 1, 2, 5, 2, 1, 3]
def baseStart_7935448 : Nat := 118140960795 + 7935448 * 2 ^ 59
def prefixEnd_7935448 : Nat := 4983230072969 + 3 ^ 40 * 7935448 * 2
def baseEnd_7935448 : Nat := 4074699032759773756905545

theorem tailTrace_7935448 : CollatzResearch.WordTrace tailWord_7935448 prefixEnd_7935448 4074699032759773756905545 := by
  unfold tailWord_7935448
  simp only [CollatzResearch.WordTrace]
  refine ⟨144714783077617318732611499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192953044103489758310148665 144714783077617318732611499)
  ·
    refine ⟨217072174616425978098917249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144714783077617318732611499 217072174616425978098917249)
    ·
      refine ⟨162804130962319483574187937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217072174616425978098917249 162804130962319483574187937)
      ·
        refine ⟨122103098221739612680640953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162804130962319483574187937 122103098221739612680640953)
        ·
          refine ⟨91577323666304709510480715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122103098221739612680640953 91577323666304709510480715)
          ·
            refine ⟨137365985499457064265721073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91577323666304709510480715 137365985499457064265721073)
            ·
              refine ⟨103024489124592798199290805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137365985499457064265721073 103024489124592798199290805)
              ·
                refine ⟨9658545855430574831183513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103024489124592798199290805 9658545855430574831183513)
                ·
                  refine ⟨7243909391572931123387635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9658545855430574831183513 7243909391572931123387635)
                  ·
                    refine ⟨10865864087359396685081453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7243909391572931123387635 10865864087359396685081453)
                    ·
                      refine ⟨4074699032759773756905545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10865864087359396685081453 4074699032759773756905545)
                      ·
                        rfl

theorem cell23_7935448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_7935448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935448 prefixEnd_7935448 := by exact prefixLift 7935448
  have htrace : WordTrace (prefixWord ++ tailWord_7935448) baseStart_7935448 baseEnd_7935448 := by
    simpa [prefixWord, tailWord_7935448, baseEnd_7935448] using wordTrace_append hprefix tailTrace_7935448
  have hstable : (prefixWord ++ tailWord_7935448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935448).length < 2 ^ (prefixWord ++ tailWord_7935448).sum := by decide
  have hdescent : baseEnd_7935448 < baseStart_7935448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935461 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 2, 2, 5]
def baseStart_7935461 : Nat := 118140960795 + 7935461 * 2 ^ 59
def prefixEnd_7935461 : Nat := 4983230072969 + 3 ^ 40 * 7935461 * 2
def baseEnd_7935461 : Nat := 4074705708008282206042985

theorem tailTrace_7935461 : CollatzResearch.WordTrace tailWord_7935461 prefixEnd_7935461 4074705708008282206042985 := by
  unfold tailWord_7935461
  simp only [CollatzResearch.WordTrace]
  refine ⟨289430040304187540685446237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192953360202791693790297491 289430040304187540685446237)
  ·
    refine ⟨108536265114070327757042339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289430040304187540685446237 108536265114070327757042339)
    ·
      refine ⟨162804397671105491635563509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108536265114070327757042339 162804397671105491635563509)
      ·
        refine ⟨15262912281666139840834079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162804397671105491635563509 15262912281666139840834079)
        ·
          refine ⟨22894368422499209761251119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15262912281666139840834079 22894368422499209761251119)
          ·
            refine ⟨34341552633748814641876679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22894368422499209761251119 34341552633748814641876679)
            ·
              refine ⟨51512328950623221962815019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34341552633748814641876679 51512328950623221962815019)
              ·
                refine ⟨77268493425934832944222529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51512328950623221962815019 77268493425934832944222529)
                ·
                  refine ⟨57951370069451124708166897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77268493425934832944222529 57951370069451124708166897)
                  ·
                    refine ⟨43463527552088343531125173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57951370069451124708166897 43463527552088343531125173)
                    ·
                      refine ⟨4074705708008282206042985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43463527552088343531125173 4074705708008282206042985)
                      ·
                        rfl

theorem cell23_7935461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_7935461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935461 prefixEnd_7935461 := by exact prefixLift 7935461
  have htrace : WordTrace (prefixWord ++ tailWord_7935461) baseStart_7935461 baseEnd_7935461 := by
    simpa [prefixWord, tailWord_7935461, baseEnd_7935461] using wordTrace_append hprefix tailTrace_7935461
  have hstable : (prefixWord ++ tailWord_7935461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935461).length < 2 ^ (prefixWord ++ tailWord_7935461).sum := by decide
  have hdescent : baseEnd_7935461 < baseStart_7935461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935466 : List Nat := [3, 1, 3, 1, 5, 1, 1, 3, 1, 2, 2]
def baseStart_7935466 : Nat := 118140960795 + 7935466 * 2 ^ 59
def prefixEnd_7935466 : Nat := 4983230072969 + 3 ^ 40 * 7935466 * 2
def baseEnd_7935466 : Nat := 4074708275411554686480463

theorem tailTrace_7935466 : CollatzResearch.WordTrace tailWord_7935466 prefixEnd_7935466 4074708275411554686480463 := by
  unfold tailWord_7935466
  simp only [CollatzResearch.WordTrace]
  refine ⟨72357555667292356634844563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192953481779446284359585501 72357555667292356634844563)
  ·
    refine ⟨108536333500938534952266845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72357555667292356634844563 108536333500938534952266845)
    ·
      refine ⟨40701125062851950607100067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108536333500938534952266845 40701125062851950607100067)
      ·
        refine ⟨61051687594277925910650101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40701125062851950607100067 61051687594277925910650101)
        ·
          refine ⟨5723595711963555554123447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61051687594277925910650101 5723595711963555554123447)
          ·
            refine ⟨8585393567945333331185171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5723595711963555554123447 8585393567945333331185171)
            ·
              refine ⟨12878090351917999996777757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8585393567945333331185171 12878090351917999996777757)
              ·
                refine ⟨4829283881969249998791659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12878090351917999996777757 4829283881969249998791659)
                ·
                  refine ⟨7243925822953874998187489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4829283881969249998791659 7243925822953874998187489)
                  ·
                    refine ⟨5432944367215406248640617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7243925822953874998187489 5432944367215406248640617)
                    ·
                      refine ⟨4074708275411554686480463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5432944367215406248640617 4074708275411554686480463)
                      ·
                        rfl

theorem cell23_7935466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_7935466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935466 prefixEnd_7935466 := by exact prefixLift 7935466
  have htrace : WordTrace (prefixWord ++ tailWord_7935466) baseStart_7935466 baseEnd_7935466 := by
    simpa [prefixWord, tailWord_7935466, baseEnd_7935466] using wordTrace_append hprefix tailTrace_7935466
  have hstable : (prefixWord ++ tailWord_7935466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935466).length < 2 ^ (prefixWord ++ tailWord_7935466).sum := by decide
  have hdescent : baseEnd_7935466 < baseStart_7935466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935499 : List Nat := [1, 1, 1, 1, 9, 1, 2, 1, 2, 1, 3]
def baseStart_7935499 : Nat := 118140960795 + 7935499 * 2 ^ 59
def prefixEnd_7935499 : Nat := 4983230072969 + 3 ^ 40 * 7935499 * 2
def baseEnd_7935499 : Nat := 4074725220273153057367811

theorem tailTrace_7935499 : CollatzResearch.WordTrace tailWord_7935499 prefixEnd_7935499 4074725220273153057367811 := by
  unfold tailWord_7935499
  simp only [CollatzResearch.WordTrace]
  refine ⟨289431426278049873175329551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192954284185366582116886367 289431426278049873175329551)
  ·
    refine ⟨434147139417074809762994327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289431426278049873175329551 434147139417074809762994327)
    ·
      refine ⟨651220709125612214644491491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434147139417074809762994327 651220709125612214644491491)
      ·
        refine ⟨976831063688418321966737237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651220709125612214644491491 976831063688418321966737237)
        ·
          refine ⟨5723619513799326105273851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 976831063688418321966737237 5723619513799326105273851)
          ·
            refine ⟨8585429270698989157910777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5723619513799326105273851 8585429270698989157910777)
            ·
              refine ⟨6439071953024241868433083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8585429270698989157910777 6439071953024241868433083)
              ·
                refine ⟨9658607929536362802649625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6439071953024241868433083 9658607929536362802649625)
                ·
                  refine ⟨7243955947152272101987219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9658607929536362802649625 7243955947152272101987219)
                  ·
                    refine ⟨10865933920728408152980829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7243955947152272101987219 10865933920728408152980829)
                    ·
                      refine ⟨4074725220273153057367811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10865933920728408152980829 4074725220273153057367811)
                      ·
                        rfl

theorem cell23_7935499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 2, 1, 3].length) (baseStart_7935499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935499 prefixEnd_7935499 := by exact prefixLift 7935499
  have htrace : WordTrace (prefixWord ++ tailWord_7935499) baseStart_7935499 baseEnd_7935499 := by
    simpa [prefixWord, tailWord_7935499, baseEnd_7935499] using wordTrace_append hprefix tailTrace_7935499
  have hstable : (prefixWord ++ tailWord_7935499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935499).length < 2 ^ (prefixWord ++ tailWord_7935499).sum := by decide
  have hdescent : baseEnd_7935499 < baseStart_7935499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935505 : List Nat := [1, 2, 2, 1, 1, 2, 5, 3, 2, 2, 2]
def baseStart_7935505 : Nat := 118140960795 + 7935505 * 2 ^ 59
def prefixEnd_7935505 : Nat := 4983230072969 + 3 ^ 40 * 7935505 * 2
def baseEnd_7935505 : Nat := 4074728301157080033892783

theorem tailTrace_7935505 : CollatzResearch.WordTrace tailWord_7935505 prefixEnd_7935505 4074728301157080033892783 := by
  unfold tailWord_7935505
  simp only [CollatzResearch.WordTrace]
  refine ⟨289431645116028136200047969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192954430077352090800031979 289431645116028136200047969)
  ·
    refine ⟨217073733837021102150035977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289431645116028136200047969 217073733837021102150035977)
    ·
      refine ⟨162805300377765826612526983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217073733837021102150035977 162805300377765826612526983)
      ·
        refine ⟨244207950566648739918790475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162805300377765826612526983 244207950566648739918790475)
        ·
          refine ⟨366311925849973109878185713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244207950566648739918790475 366311925849973109878185713)
          ·
            refine ⟨274733944387479832408639285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366311925849973109878185713 274733944387479832408639285)
            ·
              refine ⟨25756307286326234288309933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274733944387479832408639285 25756307286326234288309933)
              ·
                refine ⟨9658615232372337858116225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25756307286326234288309933 9658615232372337858116225)
                ·
                  refine ⟨7243961424279253393587169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9658615232372337858116225 7243961424279253393587169)
                  ·
                    refine ⟨5432971068209440045190377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7243961424279253393587169 5432971068209440045190377)
                    ·
                      refine ⟨4074728301157080033892783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5432971068209440045190377 4074728301157080033892783)
                      ·
                        rfl

theorem cell23_7935505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 2, 2].length) (baseStart_7935505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935505 prefixEnd_7935505 := by exact prefixLift 7935505
  have htrace : WordTrace (prefixWord ++ tailWord_7935505) baseStart_7935505 baseEnd_7935505 := by
    simpa [prefixWord, tailWord_7935505, baseEnd_7935505] using wordTrace_append hprefix tailTrace_7935505
  have hstable : (prefixWord ++ tailWord_7935505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935505).length < 2 ^ (prefixWord ++ tailWord_7935505).sum := by decide
  have hdescent : baseEnd_7935505 < baseStart_7935505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935545 : List Nat := [1, 2, 1, 5, 1, 2, 4, 2, 5]
def baseStart_7935545 : Nat := 118140960795 + 7935545 * 2 ^ 59
def prefixEnd_7935545 : Nat := 4983230072969 + 3 ^ 40 * 7935545 * 2
def baseEnd_7935545 : Nat := 452749871153695541932511

theorem tailTrace_7935545 : CollatzResearch.WordTrace tailWord_7935545 prefixEnd_7935545 452749871153695541932511 := by
  unfold tailWord_7935545
  simp only [CollatzResearch.WordTrace]
  refine ⟨289433104035883223031504089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192955402690588815354336059 289433104035883223031504089)
  ·
    refine ⟨217074828026912417273628067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289433104035883223031504089 217074828026912417273628067)
    ·
      refine ⟨325612242040368625910442101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217074828026912417273628067 325612242040368625910442101)
      ·
        refine ⟨30526147691284558679103947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325612242040368625910442101 30526147691284558679103947)
        ·
          refine ⟨45789221536926838018655921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30526147691284558679103947 45789221536926838018655921)
          ·
            refine ⟨34341916152695128513991941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45789221536926838018655921 34341916152695128513991941)
            ·
              refine ⟨6439109278630336596373489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34341916152695128513991941 6439109278630336596373489)
              ·
                refine ⟨4829331958972752447280117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6439109278630336596373489 4829331958972752447280117)
                ·
                  refine ⟨452749871153695541932511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4829331958972752447280117 452749871153695541932511)
                  ·
                    rfl

theorem cell23_7935545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 5].length) (baseStart_7935545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935545 prefixEnd_7935545 := by exact prefixLift 7935545
  have htrace : WordTrace (prefixWord ++ tailWord_7935545) baseStart_7935545 baseEnd_7935545 := by
    simpa [prefixWord, tailWord_7935545, baseEnd_7935545] using wordTrace_append hprefix tailTrace_7935545
  have hstable : (prefixWord ++ tailWord_7935545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935545).length < 2 ^ (prefixWord ++ tailWord_7935545).sum := by decide
  have hdescent : baseEnd_7935545 < baseStart_7935545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935551 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 5]
def baseStart_7935551 : Nat := 118140960795 + 7935551 * 2 ^ 59
def prefixEnd_7935551 : Nat := 4983230072969 + 3 ^ 40 * 7935551 * 2
def baseEnd_7935551 : Nat := 4074751921267186853917571

theorem tailTrace_7935551 : CollatzResearch.WordTrace tailWord_7935551 prefixEnd_7935551 4074751921267186853917571 := by
  unfold tailWord_7935551
  simp only [CollatzResearch.WordTrace]
  refine ⟨289433322873861486056222507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192955548582574324037481671 289433322873861486056222507)
  ·
    refine ⟨434149984310792229084333761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289433322873861486056222507 434149984310792229084333761)
    ·
      refine ⟨325612488233094171813250321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434149984310792229084333761 325612488233094171813250321)
      ·
        refine ⟨244209366174820628859937741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325612488233094171813250321 244209366174820628859937741)
        ·
          refine ⟨91578512315557735822476653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244209366174820628859937741 91578512315557735822476653)
          ·
            refine ⟨34341942118334150933428745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91578512315557735822476653 34341942118334150933428745)
            ·
              refine ⟨25756456588750613200071559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34341942118334150933428745 25756456588750613200071559)
              ·
                refine ⟨38634684883125919800107339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25756456588750613200071559 38634684883125919800107339)
                ·
                  refine ⟨57952027324688879700161009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38634684883125919800107339 57952027324688879700161009)
                  ·
                    refine ⟨43464020493516659775120757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57952027324688879700161009 43464020493516659775120757)
                    ·
                      refine ⟨4074751921267186853917571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43464020493516659775120757 4074751921267186853917571)
                      ·
                        rfl

theorem cell23_7935551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_7935551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935551 prefixEnd_7935551 := by exact prefixLift 7935551
  have htrace : WordTrace (prefixWord ++ tailWord_7935551) baseStart_7935551 baseEnd_7935551 := by
    simpa [prefixWord, tailWord_7935551, baseEnd_7935551] using wordTrace_append hprefix tailTrace_7935551
  have hstable : (prefixWord ++ tailWord_7935551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935551).length < 2 ^ (prefixWord ++ tailWord_7935551).sum := by decide
  have hdescent : baseEnd_7935551 < baseStart_7935551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935561 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 4, 1, 4]
def baseStart_7935561 : Nat := 118140960795 + 7935561 * 2 ^ 59
def prefixEnd_7935561 : Nat := 4983230072969 + 3 ^ 40 * 7935561 * 2
def baseEnd_7935561 : Nat := 4074757056073731814792525

theorem tailTrace_7935561 : CollatzResearch.WordTrace tailWord_7935561 prefixEnd_7935561 4074757056073731814792525 := by
  unfold tailWord_7935561
  simp only [CollatzResearch.WordTrace]
  refine ⟨289433687603825257764086537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192955791735883505176057691 289433687603825257764086537)
  ·
    refine ⟨217075265702868943323064903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289433687603825257764086537 217075265702868943323064903)
    ·
      refine ⟨325612898554303414984597355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217075265702868943323064903 325612898554303414984597355)
      ·
        refine ⟨488419347831455122476896033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325612898554303414984597355 488419347831455122476896033)
        ·
          refine ⟨366314510873591341857672025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488419347831455122476896033 366314510873591341857672025)
          ·
            refine ⟨274735883155193506393254019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366314510873591341857672025 274735883155193506393254019)
            ·
              refine ⟨412103824732790259589881029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274735883155193506393254019 412103824732790259589881029)
              ·
                refine ⟨77269467137398173673102693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 412103824732790259589881029 77269467137398173673102693)
                ·
                  refine ⟨14488025088262157563706755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77269467137398173673102693 14488025088262157563706755)
                  ·
                    refine ⟨21732037632393236345560133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14488025088262157563706755 21732037632393236345560133)
                    ·
                      refine ⟨4074757056073731814792525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21732037632393236345560133 4074757056073731814792525)
                      ·
                        rfl

theorem cell23_7935561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 1, 4].length) (baseStart_7935561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935561 prefixEnd_7935561 := by exact prefixLift 7935561
  have htrace : WordTrace (prefixWord ++ tailWord_7935561) baseStart_7935561 baseEnd_7935561 := by
    simpa [prefixWord, tailWord_7935561, baseEnd_7935561] using wordTrace_append hprefix tailTrace_7935561
  have hstable : (prefixWord ++ tailWord_7935561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935561).length < 2 ^ (prefixWord ++ tailWord_7935561).sum := by decide
  have hdescent : baseEnd_7935561 < baseStart_7935561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935591 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_7935591 : Nat := 118140960795 + 7935591 * 2 ^ 59
def prefixEnd_7935591 : Nat := 4983230072969 + 3 ^ 40 * 7935591 * 2
def baseEnd_7935591 : Nat := 4074772460493366697417387

theorem tailTrace_7935591 : CollatzResearch.WordTrace tailWord_7935591 prefixEnd_7935591 4074772460493366697417387 := by
  unfold tailWord_7935591
  simp only [CollatzResearch.WordTrace]
  refine ⟨289434781793716572887678627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192956521195811048591785751 289434781793716572887678627)
  ·
    refine ⟨434152172690574859331517941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289434781793716572887678627 434152172690574859331517941)
    ·
      refine ⟨40701766189741393062329807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 434152172690574859331517941 40701766189741393062329807)
      ·
        refine ⟨61052649284612089593494711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40701766189741393062329807 61052649284612089593494711)
        ·
          refine ⟨91578973926918134390242067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61052649284612089593494711 91578973926918134390242067)
          ·
            refine ⟨137368460890377201585363101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91578973926918134390242067 137368460890377201585363101)
            ·
              refine ⟨51513172833891450594511163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137368460890377201585363101 51513172833891450594511163)
              ·
                refine ⟨77269759250837175891766745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51513172833891450594511163 77269759250837175891766745)
                ·
                  refine ⟨57952319438127881918825059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77269759250837175891766745 57952319438127881918825059)
                  ·
                    refine ⟨86928479157191822878237589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57952319438127881918825059 86928479157191822878237589)
                    ·
                      refine ⟨4074772460493366697417387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86928479157191822878237589 4074772460493366697417387)
                      ·
                        rfl

theorem cell23_7935591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_7935591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935591 prefixEnd_7935591 := by exact prefixLift 7935591
  have htrace : WordTrace (prefixWord ++ tailWord_7935591) baseStart_7935591 baseEnd_7935591 := by
    simpa [prefixWord, tailWord_7935591, baseEnd_7935591] using wordTrace_append hprefix tailTrace_7935591
  have hstable : (prefixWord ++ tailWord_7935591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935591).length < 2 ^ (prefixWord ++ tailWord_7935591).sum := by decide
  have hdescent : baseEnd_7935591 < baseStart_7935591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935605 : List Nat := [1, 3, 4, 2, 1, 1, 1, 3, 3, 4]
def baseStart_7935605 : Nat := 118140960795 + 7935605 * 2 ^ 59
def prefixEnd_7935605 : Nat := 4983230072969 + 3 ^ 40 * 7935605 * 2
def baseEnd_7935605 : Nat := 1358259883074176547547441

theorem tailTrace_7935605 : CollatzResearch.WordTrace tailWord_7935605 prefixEnd_7935605 1358259883074176547547441 := by
  unfold tailWord_7935605
  simp only [CollatzResearch.WordTrace]
  refine ⟨289435292415665853278688269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192956861610443902185792179 289435292415665853278688269)
  ·
    refine ⟨108538234655874694979508101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289435292415665853278688269 108538234655874694979508101)
    ·
      refine ⟨20350918997976505308657769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108538234655874694979508101 20350918997976505308657769)
      ·
        refine ⟨15263189248482378981493327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20350918997976505308657769 15263189248482378981493327)
        ·
          refine ⟨22894783872723568472239991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15263189248482378981493327 22894783872723568472239991)
          ·
            refine ⟨34342175809085352708359987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22894783872723568472239991 34342175809085352708359987)
            ·
              refine ⟨51513263713628029062539981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34342175809085352708359987 51513263713628029062539981)
              ·
                refine ⟨19317473892610510898452493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51513263713628029062539981 19317473892610510898452493)
                ·
                  refine ⟨7244052709728941586919685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19317473892610510898452493 7244052709728941586919685)
                  ·
                    refine ⟨1358259883074176547547441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7244052709728941586919685 1358259883074176547547441)
                    ·
                      rfl

theorem cell23_7935605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_7935605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935605 prefixEnd_7935605 := by exact prefixLift 7935605
  have htrace : WordTrace (prefixWord ++ tailWord_7935605) baseStart_7935605 baseEnd_7935605 := by
    simpa [prefixWord, tailWord_7935605, baseEnd_7935605] using wordTrace_append hprefix tailTrace_7935605
  have hstable : (prefixWord ++ tailWord_7935605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935605).length < 2 ^ (prefixWord ++ tailWord_7935605).sum := by decide
  have hdescent : baseEnd_7935605 < baseStart_7935605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935621 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 1, 2, 6]
def baseStart_7935621 : Nat := 118140960795 + 7935621 * 2 ^ 59
def prefixEnd_7935621 : Nat := 4983230072969 + 3 ^ 40 * 7935621 * 2
def baseEnd_7935621 : Nat := 4074787864913001580042249

theorem tailTrace_7935621 : CollatzResearch.WordTrace tailWord_7935621 prefixEnd_7935621 4074787864913001580042249 := by
  unfold tailWord_7935621
  simp only [CollatzResearch.WordTrace]
  refine ⟨289435875983607888011270717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192957250655738592007513811 289435875983607888011270717)
  ·
    refine ⟨108538453493852958004226519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289435875983607888011270717 108538453493852958004226519)
    ·
      refine ⟨162807680240779437006339779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108538453493852958004226519 162807680240779437006339779)
      ·
        refine ⟨244211520361169155509509669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162807680240779437006339779 244211520361169155509509669)
        ·
          refine ⟨45789660067719216658033063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244211520361169155509509669 45789660067719216658033063)
          ·
            refine ⟨68684490101578824987049595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45789660067719216658033063 68684490101578824987049595)
            ·
              refine ⟨103026735152368237480574393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68684490101578824987049595 103026735152368237480574393)
              ·
                refine ⟨77270051364276178110430795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103026735152368237480574393 77270051364276178110430795)
                ·
                  refine ⟨115905077046414267165646193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77270051364276178110430795 115905077046414267165646193)
                  ·
                    refine ⟨86928807784810700374234645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115905077046414267165646193 86928807784810700374234645)
                    ·
                      refine ⟨4074787864913001580042249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86928807784810700374234645 4074787864913001580042249)
                      ·
                        rfl

theorem cell23_7935621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_7935621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935621 prefixEnd_7935621 := by exact prefixLift 7935621
  have htrace : WordTrace (prefixWord ++ tailWord_7935621) baseStart_7935621 baseEnd_7935621 := by
    simpa [prefixWord, tailWord_7935621, baseEnd_7935621] using wordTrace_append hprefix tailTrace_7935621
  have hstable : (prefixWord ++ tailWord_7935621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935621).length < 2 ^ (prefixWord ++ tailWord_7935621).sum := by decide
  have hdescent : baseEnd_7935621 < baseStart_7935621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935656 : List Nat := [2, 1, 7, 1, 1, 2, 1, 1, 3, 4]
def baseStart_7935656 : Nat := 118140960795 + 7935656 * 2 ^ 59
def prefixEnd_7935656 : Nat := 4983230072969 + 3 ^ 40 * 7935656 * 2
def baseEnd_7935656 : Nat := 1358268612245302981034863

theorem tailTrace_7935656 : CollatzResearch.WordTrace tailWord_7935656 prefixEnd_7935656 1358268612245302981034863 := by
  unfold tailWord_7935656
  simp only [CollatzResearch.WordTrace]
  refine ⟨144718576269240544494397411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192958101692320725992529881 144718576269240544494397411)
  ·
    refine ⟨217077864403860816741596117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144718576269240544494397411 217077864403860816741596117)
    ·
      refine ⟨5087762446965487892381159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 217077864403860816741596117 5087762446965487892381159)
      ·
        refine ⟨7631643670448231838571739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5087762446965487892381159 7631643670448231838571739)
        ·
          refine ⟨11447465505672347757857609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7631643670448231838571739 11447465505672347757857609)
          ·
            refine ⟨8585599129254260818393207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11447465505672347757857609 8585599129254260818393207)
            ·
              refine ⟨12878398693881391227589811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8585599129254260818393207 12878398693881391227589811)
              ·
                refine ⟨19317598040822086841384717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12878398693881391227589811 19317598040822086841384717)
                ·
                  refine ⟨7244099265308282565519269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19317598040822086841384717 7244099265308282565519269)
                  ·
                    refine ⟨1358268612245302981034863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7244099265308282565519269 1358268612245302981034863)
                    ·
                      rfl

theorem cell23_7935656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_7935656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935656 prefixEnd_7935656 := by exact prefixLift 7935656
  have htrace : WordTrace (prefixWord ++ tailWord_7935656) baseStart_7935656 baseEnd_7935656 := by
    simpa [prefixWord, tailWord_7935656, baseEnd_7935656] using wordTrace_append hprefix tailTrace_7935656
  have hstable : (prefixWord ++ tailWord_7935656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935656).length < 2 ^ (prefixWord ++ tailWord_7935656).sum := by decide
  have hdescent : baseEnd_7935656 < baseStart_7935656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935669 : List Nat := [1, 3, 3, 3, 3, 1, 2, 1, 6]
def baseStart_7935669 : Nat := 118140960795 + 7935669 * 2 ^ 59
def prefixEnd_7935669 : Nat := 4983230072969 + 3 ^ 40 * 7935669 * 2
def baseEnd_7935669 : Nat := 452756945776046376915781

theorem tailTrace_7935669 : CollatzResearch.WordTrace tailWord_7935669 prefixEnd_7935669 452756945776046376915781 := by
  unfold tailWord_7935669
  simp only [CollatzResearch.WordTrace]
  refine ⟨289437626687433992209018061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192958417791622661472678707 289437626687433992209018061)
  ·
    refine ⟨108539110007787747078381773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289437626687433992209018061 108539110007787747078381773)
    ·
      refine ⟨40702166252920405154393165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108539110007787747078381773 40702166252920405154393165)
      ·
        refine ⟨15263312344845151932897437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40702166252920405154393165 15263312344845151932897437)
        ·
          refine ⟨5723742129316931974836539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15263312344845151932897437 5723742129316931974836539)
          ·
            refine ⟨8585613193975397962254809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5723742129316931974836539 8585613193975397962254809)
            ·
              refine ⟨6439209895481548471691107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8585613193975397962254809 6439209895481548471691107)
              ·
                refine ⟨9658814843222322707536661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6439209895481548471691107 9658814843222322707536661)
                ·
                  refine ⟨452756945776046376915781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9658814843222322707536661 452756945776046376915781)
                  ·
                    rfl

theorem cell23_7935669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 6].length) (baseStart_7935669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935669 prefixEnd_7935669 := by exact prefixLift 7935669
  have htrace : WordTrace (prefixWord ++ tailWord_7935669) baseStart_7935669 baseEnd_7935669 := by
    simpa [prefixWord, tailWord_7935669, baseEnd_7935669] using wordTrace_append hprefix tailTrace_7935669
  have hstable : (prefixWord ++ tailWord_7935669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935669).length < 2 ^ (prefixWord ++ tailWord_7935669).sum := by decide
  have hdescent : baseEnd_7935669 < baseStart_7935669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935705 : List Nat := [1, 2, 1, 2, 3, 5, 1, 1, 1, 1, 5]
def baseStart_7935705 : Nat := 118140960795 + 7935705 * 2 ^ 59
def prefixEnd_7935705 : Nat := 4983230072969 + 3 ^ 40 * 7935705 * 2
def baseEnd_7935705 : Nat := 4074830997287979251391863

theorem tailTrace_7935705 : CollatzResearch.WordTrace tailWord_7935705 prefixEnd_7935705 4074830997287979251391863 := by
  unfold tailWord_7935705
  simp only [CollatzResearch.WordTrace]
  refine ⟨289438939715303570357328569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192959293143535713571552379 289438939715303570357328569)
  ·
    refine ⟨217079204786477677767996427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289438939715303570357328569 217079204786477677767996427)
    ·
      refine ⟨325618807179716516651994641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217079204786477677767996427 325618807179716516651994641)
      ·
        refine ⟨244214105384787387488995981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325618807179716516651994641 244214105384787387488995981)
        ·
          refine ⟨91580289519295270308373493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244214105384787387488995981 91580289519295270308373493)
          ·
            refine ⟨8585652142433931591410015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91580289519295270308373493 8585652142433931591410015)
            ·
              refine ⟨12878478213650897387115023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8585652142433931591410015 12878478213650897387115023)
              ·
                refine ⟨19317717320476346080672535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12878478213650897387115023 19317717320476346080672535)
                ·
                  refine ⟨28976575980714519121008803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19317717320476346080672535 28976575980714519121008803)
                  ·
                    refine ⟨43464863971071778681513205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28976575980714519121008803 43464863971071778681513205)
                    ·
                      refine ⟨4074830997287979251391863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43464863971071778681513205 4074830997287979251391863)
                      ·
                        rfl

theorem cell23_7935705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 1, 5].length) (baseStart_7935705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935705 prefixEnd_7935705 := by exact prefixLift 7935705
  have htrace : WordTrace (prefixWord ++ tailWord_7935705) baseStart_7935705 baseEnd_7935705 := by
    simpa [prefixWord, tailWord_7935705, baseEnd_7935705] using wordTrace_append hprefix tailTrace_7935705
  have hstable : (prefixWord ++ tailWord_7935705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935705).length < 2 ^ (prefixWord ++ tailWord_7935705).sum := by decide
  have hdescent : baseEnd_7935705 < baseStart_7935705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935708 : List Nat := [2, 2, 5, 1, 13]
def baseStart_7935708 : Nat := 118140960795 + 7935708 * 2 ^ 59
def prefixEnd_7935708 : Nat := 4983230072969 + 3 ^ 40 * 7935708 * 2
def baseEnd_7935708 : Nat := 5589619393319537365781

theorem tailTrace_7935708 : CollatzResearch.WordTrace tailWord_7935708 prefixEnd_7935708 5589619393319537365781 := by
  unfold tailWord_7935708
  simp only [CollatzResearch.WordTrace]
  refine ⟨144719524567146350934843889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192959366089528467913125185 144719524567146350934843889)
  ·
    refine ⟨108539643425359763201132917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144719524567146350934843889 108539643425359763201132917)
    ·
      refine ⟨10175591571127477800106211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108539643425359763201132917 10175591571127477800106211)
      ·
        refine ⟨15263387356691216700159317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10175591571127477800106211 15263387356691216700159317)
        ·
          refine ⟨5589619393319537365781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 15263387356691216700159317 5589619393319537365781)
          ·
            rfl

theorem cell23_7935708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 13].length) (baseStart_7935708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935708 prefixEnd_7935708 := by exact prefixLift 7935708
  have htrace : WordTrace (prefixWord ++ tailWord_7935708) baseStart_7935708 baseEnd_7935708 := by
    simpa [prefixWord, tailWord_7935708, baseEnd_7935708] using wordTrace_append hprefix tailTrace_7935708
  have hstable : (prefixWord ++ tailWord_7935708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935708).length < 2 ^ (prefixWord ++ tailWord_7935708).sum := by decide
  have hdescent : baseEnd_7935708 < baseStart_7935708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935713 : List Nat := [1, 2, 3, 1, 6, 1, 2, 2, 1, 1, 3]
def baseStart_7935713 : Nat := 118140960795 + 7935713 * 2 ^ 59
def prefixEnd_7935713 : Nat := 4983230072969 + 3 ^ 40 * 7935713 * 2
def baseEnd_7935713 : Nat := 4074835105133215220091827

theorem tailTrace_7935713 : CollatzResearch.WordTrace tailWord_7935713 prefixEnd_7935713 4074835105133215220091827 := by
  unfold tailWord_7935713
  simp only [CollatzResearch.WordTrace]
  refine ⟨289439231499274587723619793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192959487666183058482413195 289439231499274587723619793)
  ·
    refine ⟨217079423624455940792714845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289439231499274587723619793 217079423624455940792714845)
    ·
      refine ⟨81404783859170977797268067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217079423624455940792714845 81404783859170977797268067)
      ·
        refine ⟨122107175788756466695902101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81404783859170977797268067 122107175788756466695902101)
        ·
          refine ⟨5723773865097959376370411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 122107175788756466695902101 5723773865097959376370411)
          ·
            refine ⟨8585660797646939064555617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5723773865097959376370411 8585660797646939064555617)
            ·
              refine ⟨6439245598235204298416713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8585660797646939064555617 6439245598235204298416713)
              ·
                refine ⟨4829434198676403223812535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6439245598235204298416713 4829434198676403223812535)
                ·
                  refine ⟨7244151298014604835718803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4829434198676403223812535 7244151298014604835718803)
                  ·
                    refine ⟨10866226947021907253578205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7244151298014604835718803 10866226947021907253578205)
                    ·
                      refine ⟨4074835105133215220091827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10866226947021907253578205 4074835105133215220091827)
                      ·
                        rfl

theorem cell23_7935713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_7935713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935713 prefixEnd_7935713 := by exact prefixLift 7935713
  have htrace : WordTrace (prefixWord ++ tailWord_7935713) baseStart_7935713 baseEnd_7935713 := by
    simpa [prefixWord, tailWord_7935713, baseEnd_7935713] using wordTrace_append hprefix tailTrace_7935713
  have hstable : (prefixWord ++ tailWord_7935713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935713).length < 2 ^ (prefixWord ++ tailWord_7935713).sum := by decide
  have hdescent : baseEnd_7935713 < baseStart_7935713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935725 : List Nat := [1, 5, 1, 2, 1, 4, 1, 8]
def baseStart_7935725 : Nat := 118140960795 + 7935725 * 2 ^ 59
def prefixEnd_7935725 : Nat := 4983230072969 + 3 ^ 40 * 7935725 * 2
def baseEnd_7935725 : Nat := 150920046922261821227473

theorem tailTrace_7935725 : CollatzResearch.WordTrace tailWord_7935725 prefixEnd_7935725 150920046922261821227473 := by
  unfold tailWord_7935725
  simp only [CollatzResearch.WordTrace]
  refine ⟨289439669175231113773056629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192959779450154075848704419 289439669175231113773056629)
  ·
    refine ⟨27134968985177916916224059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289439669175231113773056629 27134968985177916916224059)
    ·
      refine ⟨40702453477766875374336089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27134968985177916916224059 40702453477766875374336089)
      ·
        refine ⟨30526840108325156530752067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40702453477766875374336089 30526840108325156530752067)
        ·
          refine ⟨45790260162487734796128101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30526840108325156530752067 45790260162487734796128101)
          ·
            refine ⟨8585673780466450274274019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45790260162487734796128101 8585673780466450274274019)
            ·
              refine ⟨12878510670699675411411029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8585673780466450274274019 12878510670699675411411029)
              ·
                refine ⟨150920046922261821227473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12878510670699675411411029 150920046922261821227473)
                ·
                  rfl

theorem cell23_7935725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 8].length) (baseStart_7935725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935725 prefixEnd_7935725 := by exact prefixLift 7935725
  have htrace : WordTrace (prefixWord ++ tailWord_7935725) baseStart_7935725 baseEnd_7935725 := by
    simpa [prefixWord, tailWord_7935725, baseEnd_7935725] using wordTrace_append hprefix tailTrace_7935725
  have hstable : (prefixWord ++ tailWord_7935725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935725).length < 2 ^ (prefixWord ++ tailWord_7935725).sum := by decide
  have hdescent : baseEnd_7935725 < baseStart_7935725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935742 : List Nat := [4, 2, 2, 1, 3, 1, 3, 7]
def baseStart_7935742 : Nat := 118140960795 + 7935742 * 2 ^ 59
def prefixEnd_7935742 : Nat := 4983230072969 + 3 ^ 40 * 7935742 * 2
def baseEnd_7935742 : Nat := 150920370224896133578859

theorem tailTrace_7935742 : CollatzResearch.WordTrace tailWord_7935742 prefixEnd_7935742 150920370224896133578859 := by
  unfold tailWord_7935742
  simp only [CollatzResearch.WordTrace]
  refine ⟨36180036152021190709553185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192960192810779683784283653 36180036152021190709553185)
  ·
    refine ⟨27135027114015893032164889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36180036152021190709553185 27135027114015893032164889)
    ·
      refine ⟨20351270335511919774123667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27135027114015893032164889 20351270335511919774123667)
      ·
        refine ⟨30526905503267879661185501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20351270335511919774123667 30526905503267879661185501)
        ·
          refine ⟨11447589563725454872944563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30526905503267879661185501 11447589563725454872944563)
          ·
            refine ⟨17171384345588182309416845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11447589563725454872944563 17171384345588182309416845)
            ·
              refine ⟨6439269129595568366031317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17171384345588182309416845 6439269129595568366031317)
              ·
                refine ⟨150920370224896133578859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6439269129595568366031317 150920370224896133578859)
                ·
                  rfl

theorem cell23_7935742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 7].length) (baseStart_7935742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935742 prefixEnd_7935742 := by exact prefixLift 7935742
  have htrace : WordTrace (prefixWord ++ tailWord_7935742) baseStart_7935742 baseEnd_7935742 := by
    simpa [prefixWord, tailWord_7935742, baseEnd_7935742] using wordTrace_append hprefix tailTrace_7935742
  have hstable : (prefixWord ++ tailWord_7935742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935742).length < 2 ^ (prefixWord ++ tailWord_7935742).sum := by decide
  have hdescent : baseEnd_7935742 < baseStart_7935742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935768 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 2, 6]
def baseStart_7935768 : Nat := 118140960795 + 7935768 * 2 ^ 59
def prefixEnd_7935768 : Nat := 4983230072969 + 3 ^ 40 * 7935768 * 2
def baseEnd_7935768 : Nat := 1358287782189737501634691

theorem tailTrace_7935768 : CollatzResearch.WordTrace tailWord_7935768 prefixEnd_7935768 1358287782189737501634691 := by
  unfold tailWord_7935768
  simp only [CollatzResearch.WordTrace]
  refine ⟨144720618757037666058435979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192960825009383554744581305 144720618757037666058435979)
  ·
    refine ⟨217080928135556499087653969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144720618757037666058435979 217080928135556499087653969)
    ·
      refine ⟨162810696101667374315740477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217080928135556499087653969 162810696101667374315740477)
      ·
        refine ⟨61054011038125265368402679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162810696101667374315740477 61054011038125265368402679)
        ·
          refine ⟨91581016557187898052604019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61054011038125265368402679 91581016557187898052604019)
          ·
            refine ⟨137371524835781847078906029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91581016557187898052604019 137371524835781847078906029)
            ·
              refine ⟨51514321813418192654589761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137371524835781847078906029 51514321813418192654589761)
              ·
                refine ⟨38635741360063644490942321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51514321813418192654589761 38635741360063644490942321)
                ·
                  refine ⟨28976806020047733368206741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38635741360063644490942321 28976806020047733368206741)
                  ·
                    refine ⟨1358287782189737501634691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28976806020047733368206741 1358287782189737501634691)
                    ·
                      rfl

theorem cell23_7935768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_7935768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935768 prefixEnd_7935768 := by exact prefixLift 7935768
  have htrace : WordTrace (prefixWord ++ tailWord_7935768) baseStart_7935768 baseEnd_7935768 := by
    simpa [prefixWord, tailWord_7935768, baseEnd_7935768] using wordTrace_append hprefix tailTrace_7935768
  have hstable : (prefixWord ++ tailWord_7935768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935768).length < 2 ^ (prefixWord ++ tailWord_7935768).sum := by decide
  have hdescent : baseEnd_7935768 < baseStart_7935768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935796 : List Nat := [2, 5, 1, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_7935796 : Nat := 118140960795 + 7935796 * 2 ^ 59
def prefixEnd_7935796 : Nat := 4983230072969 + 3 ^ 40 * 7935796 * 2
def baseEnd_7935796 : Nat := 4074877724027538395353945

theorem tailTrace_7935796 : CollatzResearch.WordTrace tailWord_7935796 prefixEnd_7935796 4074877724027538395353945 := by
  unfold tailWord_7935796
  simp only [CollatzResearch.WordTrace]
  refine ⟨144721129378986946449445621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192961505838649261932594161 144721129378986946449445621)
  ·
    refine ⟨13567605879280026229635527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144721129378986946449445621 13567605879280026229635527)
    ·
      refine ⟨20351408818920039344453291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13567605879280026229635527 20351408818920039344453291)
      ·
        refine ⟨30527113228380059016679937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20351408818920039344453291 30527113228380059016679937)
        ·
          refine ⟨22895334921285044262509953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30527113228380059016679937 22895334921285044262509953)
          ·
            refine ⟨17171501190963783196882465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22895334921285044262509953 17171501190963783196882465)
            ·
              refine ⟨12878625893222837397661849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17171501190963783196882465 12878625893222837397661849)
              ·
                refine ⟨9658969419917128048246387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12878625893222837397661849 9658969419917128048246387)
                ·
                  refine ⟨14488454129875692072369581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9658969419917128048246387 14488454129875692072369581)
                  ·
                    refine ⟨5433170298703384527138593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14488454129875692072369581 5433170298703384527138593)
                    ·
                      refine ⟨4074877724027538395353945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5433170298703384527138593 4074877724027538395353945)
                      ·
                        rfl

theorem cell23_7935796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_7935796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935796 prefixEnd_7935796 := by exact prefixLift 7935796
  have htrace : WordTrace (prefixWord ++ tailWord_7935796) baseStart_7935796 baseEnd_7935796 := by
    simpa [prefixWord, tailWord_7935796, baseEnd_7935796] using wordTrace_append hprefix tailTrace_7935796
  have hstable : (prefixWord ++ tailWord_7935796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935796).length < 2 ^ (prefixWord ++ tailWord_7935796).sum := by decide
  have hdescent : baseEnd_7935796 < baseStart_7935796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935843 : List Nat := [1, 1, 1, 5, 4, 2, 2, 1, 2, 2, 2]
def baseStart_7935843 : Nat := 118140960795 + 7935843 * 2 ^ 59
def prefixEnd_7935843 : Nat := 4983230072969 + 3 ^ 40 * 7935843 * 2
def baseEnd_7935843 : Nat := 4074901857618299711466229

theorem tailTrace_7935843 : CollatzResearch.WordTrace tailWord_7935843 prefixEnd_7935843 4074901857618299711466229 := by
  unfold tailWord_7935843
  simp only [CollatzResearch.WordTrace]
  refine ⟨289443972988803619925852183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192962648659202413283901455 289443972988803619925852183)
  ·
    refine ⟨434165959483205429888778275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289443972988803619925852183 434165959483205429888778275)
    ·
      refine ⟨651248939224808144833167413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434165959483205429888778275 651248939224808144833167413)
      ·
        refine ⟨61054588052325763578109445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 651248939224808144833167413 61054588052325763578109445)
        ·
          refine ⟨11447735259811080670895521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61054588052325763578109445 11447735259811080670895521)
          ·
            refine ⟨8585801444858310503171641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11447735259811080670895521 8585801444858310503171641)
            ·
              refine ⟨6439351083643732877378731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8585801444858310503171641 6439351083643732877378731)
              ·
                refine ⟨9659026625465599316068097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6439351083643732877378731 9659026625465599316068097)
                ·
                  refine ⟨7244269969099199487051073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9659026625465599316068097 7244269969099199487051073)
                  ·
                    refine ⟨5433202476824399615288305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7244269969099199487051073 5433202476824399615288305)
                    ·
                      refine ⟨4074901857618299711466229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5433202476824399615288305 4074901857618299711466229)
                      ·
                        rfl

theorem cell23_7935843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_7935843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935843 prefixEnd_7935843 := by exact prefixLift 7935843
  have htrace : WordTrace (prefixWord ++ tailWord_7935843) baseStart_7935843 baseEnd_7935843 := by
    simpa [prefixWord, tailWord_7935843, baseEnd_7935843] using wordTrace_append hprefix tailTrace_7935843
  have hstable : (prefixWord ++ tailWord_7935843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935843).length < 2 ^ (prefixWord ++ tailWord_7935843).sum := by decide
  have hdescent : baseEnd_7935843 < baseStart_7935843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935868 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_7935868 : Nat := 118140960795 + 7935868 * 2 ^ 59
def prefixEnd_7935868 : Nat := 4983230072969 + 3 ^ 40 * 7935868 * 2
def baseEnd_7935868 : Nat := 4074914694634662113653613

theorem tailTrace_7935868 : CollatzResearch.WordTrace tailWord_7935868 prefixEnd_7935868 4074914694634662113653613 := by
  unfold tailWord_7935868
  simp only [CollatzResearch.WordTrace]
  refine ⟨144722442406856524597756129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192963256542475366130341505 144722442406856524597756129)
  ·
    refine ⟨108541831805142393448317097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144722442406856524597756129 108541831805142393448317097)
    ·
      refine ⟨81406373853856795086237823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108541831805142393448317097 81406373853856795086237823)
      ·
        refine ⟨122109560780785192629356735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81406373853856795086237823 122109560780785192629356735)
        ·
          refine ⟨183164341171177788944035103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122109560780785192629356735 183164341171177788944035103)
          ·
            refine ⟨274746511756766683416052655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183164341171177788944035103 274746511756766683416052655)
            ·
              refine ⟨412119767635150025124078983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274746511756766683416052655 412119767635150025124078983)
              ·
                refine ⟨618179651452725037686118475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412119767635150025124078983 618179651452725037686118475)
                ·
                  refine ⟨927269477179087556529177713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 618179651452725037686118475 927269477179087556529177713)
                  ·
                    refine ⟨695452107884315667396883285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 927269477179087556529177713 695452107884315667396883285)
                    ·
                      refine ⟨4074914694634662113653613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 695452107884315667396883285 4074914694634662113653613)
                      ·
                        rfl

theorem cell23_7935868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_7935868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935868 prefixEnd_7935868 := by exact prefixLift 7935868
  have htrace : WordTrace (prefixWord ++ tailWord_7935868) baseStart_7935868 baseEnd_7935868 := by
    simpa [prefixWord, tailWord_7935868, baseEnd_7935868] using wordTrace_append hprefix tailTrace_7935868
  have hstable : (prefixWord ++ tailWord_7935868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935868).length < 2 ^ (prefixWord ++ tailWord_7935868).sum := by decide
  have hdescent : baseEnd_7935868 < baseStart_7935868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935972 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 2, 6, 2]
def baseStart_7935972 : Nat := 118140960795 + 7935972 * 2 ^ 59
def prefixEnd_7935972 : Nat := 4983230072969 + 3 ^ 40 * 7935972 * 2
def baseEnd_7935972 : Nat := 4074968096622729706753135

theorem tailTrace_7935972 : CollatzResearch.WordTrace tailWord_7935972 prefixEnd_7935972 4074968096622729706753135 := by
  unfold tailWord_7935972
  simp only [CollatzResearch.WordTrace]
  refine ⟨144724339002668137478649085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192965785336890849971532113 144724339002668137478649085)
  ·
    refine ⟨54271627126000551554493407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144724339002668137478649085 54271627126000551554493407)
    ·
      refine ⟨81407440689000827331740111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54271627126000551554493407 81407440689000827331740111)
      ·
        refine ⟨122111161033501240997610167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81407440689000827331740111 122111161033501240997610167)
        ·
          refine ⟨183166741550251861496415251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122111161033501240997610167 183166741550251861496415251)
          ·
            refine ⟨274750112325377792244622877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183166741550251861496415251 274750112325377792244622877)
            ·
              refine ⟨103031292122016672091733579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274750112325377792244622877 103031292122016672091733579)
              ·
                refine ⟨154546938183025008137600369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103031292122016672091733579 154546938183025008137600369)
                ·
                  refine ⟨115910203637268756103200277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154546938183025008137600369 115910203637268756103200277)
                  ·
                    refine ⟨5433290795496972942337513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115910203637268756103200277 5433290795496972942337513)
                    ·
                      refine ⟨4074968096622729706753135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5433290795496972942337513 4074968096622729706753135)
                      ·
                        rfl

theorem cell23_7935972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_7935972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7935972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7935972 prefixEnd_7935972 := by exact prefixLift 7935972
  have htrace : WordTrace (prefixWord ++ tailWord_7935972) baseStart_7935972 baseEnd_7935972 := by
    simpa [prefixWord, tailWord_7935972, baseEnd_7935972] using wordTrace_append hprefix tailTrace_7935972
  have hstable : (prefixWord ++ tailWord_7935972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935972).length < 2 ^ (prefixWord ++ tailWord_7935972).sum := by decide
  have hdescent : baseEnd_7935972 < baseStart_7935972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936020 : List Nat := [2, 4, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_7936020 : Nat := 118140960795 + 7936020 * 2 ^ 59
def prefixEnd_7936020 : Nat := 4983230072969 + 3 ^ 40 * 7936020 * 2
def baseEnd_7936020 : Nat := 1358330914564715172984305

theorem tailTrace_7936020 : CollatzResearch.WordTrace tailWord_7936020 prefixEnd_7936020 1358330914564715172984305 := by
  unfold tailWord_7936020
  simp only [CollatzResearch.WordTrace]
  refine ⟨144725214354581189577522757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192966952472774919436697009 144725214354581189577522757)
  ·
    refine ⟨27135977691483973045785517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144725214354581189577522757 27135977691483973045785517)
    ·
      refine ⟨10175991634306489892169569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27135977691483973045785517 10175991634306489892169569)
      ·
        refine ⟨7631993725729867419127177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10175991634306489892169569 7631993725729867419127177)
        ·
          refine ⟨5723995294297400564345383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7631993725729867419127177 5723995294297400564345383)
          ·
            refine ⟨8585992941446100846518075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5723995294297400564345383 8585992941446100846518075)
            ·
              refine ⟨12878989412169151269777113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8585992941446100846518075 12878989412169151269777113)
              ·
                refine ⟨9659242059126863452332835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12878989412169151269777113 9659242059126863452332835)
                ·
                  refine ⟨14488863088690295178499253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9659242059126863452332835 14488863088690295178499253)
                  ·
                    refine ⟨1358330914564715172984305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14488863088690295178499253 1358330914564715172984305)
                    ·
                      rfl

theorem cell23_7936020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_7936020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936020 prefixEnd_7936020 := by exact prefixLift 7936020
  have htrace : WordTrace (prefixWord ++ tailWord_7936020) baseStart_7936020 baseEnd_7936020 := by
    simpa [prefixWord, tailWord_7936020, baseEnd_7936020] using wordTrace_append hprefix tailTrace_7936020
  have hstable : (prefixWord ++ tailWord_7936020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936020).length < 2 ^ (prefixWord ++ tailWord_7936020).sum := by decide
  have hdescent : baseEnd_7936020 < baseStart_7936020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936023 : List Nat := [1, 1, 3, 5, 3, 1, 1, 2, 1, 1, 4]
def baseStart_7936023 : Nat := 118140960795 + 7936023 * 2 ^ 59
def prefixEnd_7936023 : Nat := 4983230072969 + 3 ^ 40 * 7936023 * 2
def baseEnd_7936023 : Nat := 4074994284136109007215401

theorem tailTrace_7936023 : CollatzResearch.WordTrace tailWord_7936023 prefixEnd_7936023 4074994284136109007215401 := by
  unfold tailWord_7936023
  simp only [CollatzResearch.WordTrace]
  refine ⟨289450538128151510667404723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192967025418767673778269815 289450538128151510667404723)
  ·
    refine ⟨434175807192227266001107085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289450538128151510667404723 434175807192227266001107085)
    ·
      refine ⟨162815927697085224750415157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434175807192227266001107085 162815927697085224750415157)
      ·
        refine ⟨15263993221601739820351421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162815927697085224750415157 15263993221601739820351421)
        ·
          refine ⟨5723997458100652432631783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15263993221601739820351421 5723997458100652432631783)
          ·
            refine ⟨8585996187150978648947675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5723997458100652432631783 8585996187150978648947675)
            ·
              refine ⟨12878994280726467973421513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8585996187150978648947675 12878994280726467973421513)
              ·
                refine ⟨9659245710544850980066135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12878994280726467973421513 9659245710544850980066135)
                ·
                  refine ⟨14488868565817276470099203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9659245710544850980066135 14488868565817276470099203)
                  ·
                    refine ⟨21733302848725914705148805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14488868565817276470099203 21733302848725914705148805)
                    ·
                      refine ⟨4074994284136109007215401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21733302848725914705148805 4074994284136109007215401)
                      ·
                        rfl

theorem cell23_7936023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_7936023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936023 prefixEnd_7936023 := by exact prefixLift 7936023
  have htrace : WordTrace (prefixWord ++ tailWord_7936023) baseStart_7936023 baseEnd_7936023 := by
    simpa [prefixWord, tailWord_7936023, baseEnd_7936023] using wordTrace_append hprefix tailTrace_7936023
  have hstable : (prefixWord ++ tailWord_7936023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936023).length < 2 ^ (prefixWord ++ tailWord_7936023).sum := by decide
  have hdescent : baseEnd_7936023 < baseStart_7936023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936026 : List Nat := [3, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3]
def baseStart_7936026 : Nat := 118140960795 + 7936026 * 2 ^ 59
def prefixEnd_7936026 : Nat := 4983230072969 + 3 ^ 40 * 7936026 * 2
def baseEnd_7936026 : Nat := 4074995824578072495477887

theorem tailTrace_7936026 : CollatzResearch.WordTrace tailWord_7936026 prefixEnd_7936026 4074995824578072495477887 := by
  unfold tailWord_7936026
  simp only [CollatzResearch.WordTrace]
  refine ⟨72362661886785160544940983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192967098364760428119842621 72362661886785160544940983)
  ·
    refine ⟨108543992830177740817411475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72362661886785160544940983 108543992830177740817411475)
    ·
      refine ⟨162815989245266611226117213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108543992830177740817411475 162815989245266611226117213)
      ·
        refine ⟨61055995966974979209793955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162815989245266611226117213 61055995966974979209793955)
        ·
          refine ⟨91583993950462468814690933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61055995966974979209793955 91583993950462468814690933)
          ·
            refine ⟨8585999432855856451377275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91583993950462468814690933 8585999432855856451377275)
            ·
              refine ⟨12878999149283784677065913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8585999432855856451377275 12878999149283784677065913)
              ·
                refine ⟨9659249361962838507799435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12878999149283784677065913 9659249361962838507799435)
                ·
                  refine ⟨14488874042944257761699153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9659249361962838507799435 14488874042944257761699153)
                  ·
                    refine ⟨10866655532208193321274365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14488874042944257761699153 10866655532208193321274365)
                    ·
                      refine ⟨4074995824578072495477887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10866655532208193321274365 4074995824578072495477887)
                      ·
                        rfl

theorem cell23_7936026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_7936026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936026 prefixEnd_7936026 := by exact prefixLift 7936026
  have htrace : WordTrace (prefixWord ++ tailWord_7936026) baseStart_7936026 baseEnd_7936026 := by
    simpa [prefixWord, tailWord_7936026, baseEnd_7936026] using wordTrace_append hprefix tailTrace_7936026
  have hstable : (prefixWord ++ tailWord_7936026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936026).length < 2 ^ (prefixWord ++ tailWord_7936026).sum := by decide
  have hdescent : baseEnd_7936026 < baseStart_7936026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936057 : List Nat := [1, 2, 1, 5, 3, 2, 2, 2, 1, 2, 2]
def baseStart_7936057 : Nat := 118140960795 + 7936057 * 2 ^ 59
def prefixEnd_7936057 : Nat := 4983230072969 + 3 ^ 40 * 7936057 * 2
def baseEnd_7936057 : Nat := 4075011742478361874190245

theorem tailTrace_7936057 : CollatzResearch.WordTrace tailWord_7936057 prefixEnd_7936057 4075011742478361874190245 := by
  unfold tailWord_7936057
  simp only [CollatzResearch.WordTrace]
  refine ⟨289451778210028334474142425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192967852140018889649428283 289451778210028334474142425)
  ·
    refine ⟨217088833657521250855606819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289451778210028334474142425 217088833657521250855606819)
    ·
      refine ⟨325633250486281876283410229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217088833657521250855606819 325633250486281876283410229)
      ·
        refine ⟨30528117233088925901569709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325633250486281876283410229 30528117233088925901569709)
        ·
          refine ⟨11448043962408347213088641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30528117233088925901569709 11448043962408347213088641)
          ·
            refine ⟨8586032971806260409816481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11448043962408347213088641 8586032971806260409816481)
            ·
              refine ⟨6439524728854695307362361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8586032971806260409816481 6439524728854695307362361)
              ·
                refine ⟨4829643546641021480521771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6439524728854695307362361 4829643546641021480521771)
                ·
                  refine ⟨7244465319961532220782657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4829643546641021480521771 7244465319961532220782657)
                  ·
                    refine ⟨5433348989971149165586993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7244465319961532220782657 5433348989971149165586993)
                    ·
                      refine ⟨4075011742478361874190245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5433348989971149165586993 4075011742478361874190245)
                      ·
                        rfl

theorem cell23_7936057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_7936057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936057 prefixEnd_7936057 := by exact prefixLift 7936057
  have htrace : WordTrace (prefixWord ++ tailWord_7936057) baseStart_7936057 baseEnd_7936057 := by
    simpa [prefixWord, tailWord_7936057, baseEnd_7936057] using wordTrace_append hprefix tailTrace_7936057
  have hstable : (prefixWord ++ tailWord_7936057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936057).length < 2 ^ (prefixWord ++ tailWord_7936057).sum := by decide
  have hdescent : baseEnd_7936057 < baseStart_7936057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936075 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 6]
def baseStart_7936075 : Nat := 118140960795 + 7936075 * 2 ^ 59
def prefixEnd_7936075 : Nat := 4983230072969 + 3 ^ 40 * 7936075 * 2
def baseEnd_7936075 : Nat := 4075020985130142803765161

theorem tailTrace_7936075 : CollatzResearch.WordTrace tailWord_7936075 prefixEnd_7936075 4075020985130142803765161 := by
  unfold tailWord_7936075
  simp only [CollatzResearch.WordTrace]
  refine ⟨289452434723963123548297679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192968289815975415698865119 289452434723963123548297679)
  ·
    refine ⟨434178652085944685322446519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289452434723963123548297679 434178652085944685322446519)
    ·
      refine ⟨651267978128917027983669779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434178652085944685322446519 651267978128917027983669779)
      ·
        refine ⟨976901967193375541975504669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651267978128917027983669779 976901967193375541975504669)
        ·
          refine ⟨366338237697515828240814251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 976901967193375541975504669 366338237697515828240814251)
          ·
            refine ⟨549507356546273742361221377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366338237697515828240814251 549507356546273742361221377)
            ·
              refine ⟨412130517409705306770916033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549507356546273742361221377 412130517409705306770916033)
              ·
                refine ⟨309097888057278980078187025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412130517409705306770916033 309097888057278980078187025)
                ·
                  refine ⟨231823416042959235058640269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309097888057278980078187025 231823416042959235058640269)
                  ·
                    refine ⟨86933781016109713146990101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 231823416042959235058640269 86933781016109713146990101)
                    ·
                      refine ⟨4075020985130142803765161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86933781016109713146990101 4075020985130142803765161)
                      ·
                        rfl

theorem cell23_7936075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 6].length) (baseStart_7936075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936075 prefixEnd_7936075 := by exact prefixLift 7936075
  have htrace : WordTrace (prefixWord ++ tailWord_7936075) baseStart_7936075 baseEnd_7936075 := by
    simpa [prefixWord, tailWord_7936075, baseEnd_7936075] using wordTrace_append hprefix tailTrace_7936075
  have hstable : (prefixWord ++ tailWord_7936075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936075).length < 2 ^ (prefixWord ++ tailWord_7936075).sum := by decide
  have hdescent : baseEnd_7936075 < baseStart_7936075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936094 : List Nat := [4, 4, 1, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_7936094 : Nat := 118140960795 + 7936094 * 2 ^ 59
def prefixEnd_7936094 : Nat := 4983230072969 + 3 ^ 40 * 7936094 * 2
def baseEnd_7936094 : Nat := 4075030741262578229427575

theorem tailTrace_7936094 : CollatzResearch.WordTrace tailWord_7936094 prefixEnd_7936094 4075030741262578229427575 := by
  unfold tailWord_7936094
  simp only [CollatzResearch.WordTrace]
  refine ⟨36181640963861786224154917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192968751807262859862159557 36181640963861786224154917)
  ·
    refine ⟨6784057680724084917029047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36181640963861786224154917 6784057680724084917029047)
    ·
      refine ⟨10176086521086127375543571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6784057680724084917029047 10176086521086127375543571)
      ·
        refine ⟨15264129781629191063315357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10176086521086127375543571 15264129781629191063315357)
        ·
          refine ⟨5724048668110946648743259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15264129781629191063315357 5724048668110946648743259)
          ·
            refine ⟨8586073002166419973114889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5724048668110946648743259 8586073002166419973114889)
            ·
              refine ⟨6439554751624814979836167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8586073002166419973114889 6439554751624814979836167)
              ·
                refine ⟨9659332127437222469754251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6439554751624814979836167 9659332127437222469754251)
                ·
                  refine ⟨14488998191155833704631377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9659332127437222469754251 14488998191155833704631377)
                  ·
                    refine ⟨10866748643366875278473533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14488998191155833704631377 10866748643366875278473533)
                    ·
                      refine ⟨4075030741262578229427575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10866748643366875278473533 4075030741262578229427575)
                      ·
                        rfl

theorem cell23_7936094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_7936094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936094 prefixEnd_7936094 := by exact prefixLift 7936094
  have htrace : WordTrace (prefixWord ++ tailWord_7936094) baseStart_7936094 baseEnd_7936094 := by
    simpa [prefixWord, tailWord_7936094, baseEnd_7936094] using wordTrace_append hprefix tailTrace_7936094
  have hstable : (prefixWord ++ tailWord_7936094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936094).length < 2 ^ (prefixWord ++ tailWord_7936094).sum := by decide
  have hdescent : baseEnd_7936094 < baseStart_7936094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936119 : List Nat := [1, 1, 3, 1, 1, 5, 2, 4, 5]
def baseStart_7936119 : Nat := 118140960795 + 7936119 * 2 ^ 59
def prefixEnd_7936119 : Nat := 4983230072969 + 3 ^ 40 * 7936119 * 2
def baseEnd_7936119 : Nat := 452782619808771181290551

theorem tailTrace_7936119 : CollatzResearch.WordTrace tailWord_7936119 prefixEnd_7936119 452782619808771181290551 := by
  unfold tailWord_7936119
  simp only [CollatzResearch.WordTrace]
  refine ⟨289454039535803719062899411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192969359690535812708599607 289454039535803719062899411)
  ·
    refine ⟨434181059303705578594349117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289454039535803719062899411 434181059303705578594349117)
    ·
      refine ⟨162817897238889591972880919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434181059303705578594349117 162817897238889591972880919)
      ·
        refine ⟨244226845858334387959321379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162817897238889591972880919 244226845858334387959321379)
        ·
          refine ⟨366340268787501581938982069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244226845858334387959321379 366340268787501581938982069)
          ·
            refine ⟨34344400198828273306779569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 366340268787501581938982069 34344400198828273306779569)
            ·
              refine ⟨25758300149121204980084677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34344400198828273306779569 25758300149121204980084677)
              ·
                refine ⟨4829681277960225933765877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25758300149121204980084677 4829681277960225933765877)
                ·
                  refine ⟨452782619808771181290551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4829681277960225933765877 452782619808771181290551)
                  ·
                    rfl

theorem cell23_7936119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 5].length) (baseStart_7936119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936119 prefixEnd_7936119 := by exact prefixLift 7936119
  have htrace : WordTrace (prefixWord ++ tailWord_7936119) baseStart_7936119 baseEnd_7936119 := by
    simpa [prefixWord, tailWord_7936119, baseEnd_7936119] using wordTrace_append hprefix tailTrace_7936119
  have hstable : (prefixWord ++ tailWord_7936119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936119).length < 2 ^ (prefixWord ++ tailWord_7936119).sum := by decide
  have hdescent : baseEnd_7936119 < baseStart_7936119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936132 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 3, 7]
def baseStart_7936132 : Nat := 118140960795 + 7936132 * 2 ^ 59
def prefixEnd_7936132 : Nat := 4983230072969 + 3 ^ 40 * 7936132 * 2
def baseEnd_7936132 : Nat := 1358350084509149693584133

theorem tailTrace_7936132 : CollatzResearch.WordTrace tailWord_7936132 prefixEnd_7936132 1358350084509149693584133 := by
  unfold tailWord_7936132
  simp only [CollatzResearch.WordTrace]
  refine ⟨144727256842378311141561325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192969675789837748188748433 144727256842378311141561325)
  ·
    refine ⟨54272721315891866678085497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144727256842378311141561325 54272721315891866678085497)
    ·
      refine ⟨40704540986918900008564123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54272721315891866678085497 40704540986918900008564123)
      ·
        refine ⟨61056811480378350012846185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40704540986918900008564123 61056811480378350012846185)
        ·
          refine ⟨45792608610283762509634639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61056811480378350012846185 45792608610283762509634639)
          ·
            refine ⟨68688912915425643764451959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45792608610283762509634639 68688912915425643764451959)
            ·
              refine ⟨103033369373138465646677939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68688912915425643764451959 103033369373138465646677939)
              ·
                refine ⟨154550054059707698470016909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103033369373138465646677939 154550054059707698470016909)
                ·
                  refine ⟨57956270272390386926256341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154550054059707698470016909 57956270272390386926256341)
                  ·
                    refine ⟨1358350084509149693584133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57956270272390386926256341 1358350084509149693584133)
                    ·
                      rfl

theorem cell23_7936132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_7936132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936132 prefixEnd_7936132 := by exact prefixLift 7936132
  have htrace : WordTrace (prefixWord ++ tailWord_7936132) baseStart_7936132 baseEnd_7936132 := by
    simpa [prefixWord, tailWord_7936132, baseEnd_7936132] using wordTrace_append hprefix tailTrace_7936132
  have hstable : (prefixWord ++ tailWord_7936132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936132).length < 2 ^ (prefixWord ++ tailWord_7936132).sum := by decide
  have hdescent : baseEnd_7936132 < baseStart_7936132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936170 : List Nat := [3, 1, 5, 1, 2, 1, 3, 2, 5]
def baseStart_7936170 : Nat := 118140960795 + 7936170 * 2 ^ 59
def prefixEnd_7936170 : Nat := 4983230072969 + 3 ^ 40 * 7936170 * 2
def baseEnd_7936170 : Nat := 452785529532479992453025

theorem tailTrace_7936170 : CollatzResearch.WordTrace tailWord_7936170 prefixEnd_7936170 452785529532479992453025 := by
  unfold tailWord_7936170
  simp only [CollatzResearch.WordTrace]
  refine ⟨72363974914654738693251491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192970599772412636515337309 72363974914654738693251491)
  ·
    refine ⟨108545962371982108039877237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72363974914654738693251491 108545962371982108039877237)
    ·
      refine ⟨10176183972373322628738491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108545962371982108039877237 10176183972373322628738491)
      ·
        refine ⟨15264275958559983943107737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10176183972373322628738491 15264275958559983943107737)
        ·
          refine ⟨11448206968919987957330803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15264275958559983943107737 11448206968919987957330803)
          ·
            refine ⟨17172310453379981935996205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11448206968919987957330803 17172310453379981935996205)
            ·
              refine ⟨6439616420017493225998577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17172310453379981935996205 6439616420017493225998577)
              ·
                refine ⟨4829712315013119919498933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6439616420017493225998577 4829712315013119919498933)
                ·
                  refine ⟨452785529532479992453025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4829712315013119919498933 452785529532479992453025)
                  ·
                    rfl

theorem cell23_7936170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 5].length) (baseStart_7936170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936170 prefixEnd_7936170 := by exact prefixLift 7936170
  have htrace : WordTrace (prefixWord ++ tailWord_7936170) baseStart_7936170 baseEnd_7936170 := by
    simpa [prefixWord, tailWord_7936170, baseEnd_7936170] using wordTrace_append hprefix tailTrace_7936170
  have hstable : (prefixWord ++ tailWord_7936170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936170).length < 2 ^ (prefixWord ++ tailWord_7936170).sum := by decide
  have hdescent : baseEnd_7936170 < baseStart_7936170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936189 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 6, 2, 3]
def baseStart_7936189 : Nat := 118140960795 + 7936189 * 2 ^ 59
def prefixEnd_7936189 : Nat := 4983230072969 + 3 ^ 40 * 7936189 * 2
def baseEnd_7936189 : Nat := 4075079521924755357739637

theorem tailTrace_7936189 : CollatzResearch.WordTrace tailWord_7936189 prefixEnd_7936189 4075079521924755357739637 := by
  unfold tailWord_7936189
  simp only [CollatzResearch.WordTrace]
  refine ⟨289456592645550121017947621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192971061763700080678631747 289456592645550121017947621)
  ·
    refine ⟨54273111121040647690865179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289456592645550121017947621 54273111121040647690865179)
    ·
      refine ⟨81409666681560971536297769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54273111121040647690865179 81409666681560971536297769)
      ·
        refine ⟨61057250011170728652223327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81409666681560971536297769 61057250011170728652223327)
        ·
          refine ⟨91585875016756092978334991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61057250011170728652223327 91585875016756092978334991)
          ·
            refine ⟨137378812525134139467502487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91585875016756092978334991 137378812525134139467502487)
            ·
              refine ⟨206068218787701209201253731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137378812525134139467502487 206068218787701209201253731)
              ·
                refine ⟨309102328181551813801880597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206068218787701209201253731 309102328181551813801880597)
                ·
                  refine ⟨14489171633510241271963153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 309102328181551813801880597 14489171633510241271963153)
                  ·
                    refine ⟨10866878725132680953972365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14489171633510241271963153 10866878725132680953972365)
                    ·
                      refine ⟨4075079521924755357739637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10866878725132680953972365 4075079521924755357739637)
                      ·
                        rfl

theorem cell23_7936189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_7936189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936189 prefixEnd_7936189 := by exact prefixLift 7936189
  have htrace : WordTrace (prefixWord ++ tailWord_7936189) baseStart_7936189 baseEnd_7936189 := by
    simpa [prefixWord, tailWord_7936189, baseEnd_7936189] using wordTrace_append hprefix tailTrace_7936189
  have hstable : (prefixWord ++ tailWord_7936189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936189).length < 2 ^ (prefixWord ++ tailWord_7936189).sum := by decide
  have hdescent : baseEnd_7936189 < baseStart_7936189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936206 : List Nat := [4, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3]
def baseStart_7936206 : Nat := 118140960795 + 7936206 * 2 ^ 59
def prefixEnd_7936206 : Nat := 4983230072969 + 3 ^ 40 * 7936206 * 2
def baseEnd_7936206 : Nat := 4075088251095881791227059

theorem tailTrace_7936206 : CollatzResearch.WordTrace tailWord_7936206 prefixEnd_7936206 4075088251095881791227059 := by
  unfold tailWord_7936206
  simp only [CollatzResearch.WordTrace]
  refine ⟨36182151585811066615164559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192971475124325688614210981 36182151585811066615164559)
  ·
    refine ⟨54273227378716599922746839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36182151585811066615164559 54273227378716599922746839)
    ·
      refine ⟨81409841068074899884120259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54273227378716599922746839 81409841068074899884120259)
      ·
        refine ⟨122114761602112349826180389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81409841068074899884120259 122114761602112349826180389)
        ·
          refine ⟨22896517800396065592408823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122114761602112349826180389 22896517800396065592408823)
          ·
            refine ⟨34344776700594098388613235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22896517800396065592408823 34344776700594098388613235)
            ·
              refine ⟨51517165050891147582919853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34344776700594098388613235 51517165050891147582919853)
              ·
                refine ⟨19318936894084180343594945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51517165050891147582919853 19318936894084180343594945)
                ·
                  refine ⟨14489202670563135257696209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19318936894084180343594945 14489202670563135257696209)
                  ·
                    refine ⟨10866902002922351443272157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14489202670563135257696209 10866902002922351443272157)
                    ·
                      refine ⟨4075088251095881791227059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10866902002922351443272157 4075088251095881791227059)
                      ·
                        rfl

theorem cell23_7936206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_7936206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936206 prefixEnd_7936206 := by exact prefixLift 7936206
  have htrace : WordTrace (prefixWord ++ tailWord_7936206) baseStart_7936206 baseEnd_7936206 := by
    simpa [prefixWord, tailWord_7936206, baseEnd_7936206] using wordTrace_append hprefix tailTrace_7936206
  have hstable : (prefixWord ++ tailWord_7936206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936206).length < 2 ^ (prefixWord ++ tailWord_7936206).sum := by decide
  have hdescent : baseEnd_7936206 < baseStart_7936206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7936236 : List Nat := [2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 3]
def baseStart_7936236 : Nat := 118140960795 + 7936236 * 2 ^ 59
def prefixEnd_7936236 : Nat := 4983230072969 + 3 ^ 40 * 7936236 * 2
def baseEnd_7936236 : Nat := 4075103655515516673851921

theorem tailTrace_7936236 : CollatzResearch.WordTrace tailWord_7936236 prefixEnd_7936236 4075103655515516673851921 := by
  unfold tailWord_7936236
  simp only [CollatzResearch.WordTrace]
  refine ⟨144729153438189924022454281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192972204584253232029939041 144729153438189924022454281)
  ·
    refine ⟨108546865078642443016840711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144729153438189924022454281 108546865078642443016840711)
    ·
      refine ⟨162820297617963664525261067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108546865078642443016840711 162820297617963664525261067)
      ·
        refine ⟨244230446426945496787891601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162820297617963664525261067 244230446426945496787891601)
        ·
          refine ⟨183172834820209122590918701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244230446426945496787891601 183172834820209122590918701)
          ·
            refine ⟨68689813057578420971594513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183172834820209122590918701 68689813057578420971594513)
            ·
              refine ⟨51517359793183815728695885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68689813057578420971594513 51517359793183815728695885)
              ·
                refine ⟨19319009922443930898260957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51517359793183815728695885 19319009922443930898260957)
                ·
                  refine ⟨7244628720916474086847859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19319009922443930898260957 7244628720916474086847859)
                  ·
                    refine ⟨10866943081374711130271789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7244628720916474086847859 10866943081374711130271789)
                    ·
                      refine ⟨4075103655515516673851921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10866943081374711130271789 4075103655515516673851921)
                      ·
                        rfl

theorem cell23_7936236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 3].length) (baseStart_7936236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7936236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7936236 prefixEnd_7936236 := by exact prefixLift 7936236
  have htrace : WordTrace (prefixWord ++ tailWord_7936236) baseStart_7936236 baseEnd_7936236 := by
    simpa [prefixWord, tailWord_7936236, baseEnd_7936236] using wordTrace_append hprefix tailTrace_7936236
  have hstable : (prefixWord ++ tailWord_7936236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7936236).length < 2 ^ (prefixWord ++ tailWord_7936236).sum := by decide
  have hdescent : baseEnd_7936236 < baseStart_7936236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7936236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
