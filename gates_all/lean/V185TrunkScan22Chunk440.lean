import V185TrunkScan22Chunk439

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3923047 : List Nat := [1, 1, 5, 1, 1, 4, 3, 1, 2, 3]
def baseStart_3923047 : Nat := 118140960795 + 3923047 * 2 ^ 59
def prefixEnd_3923047 : Nat := 4983230072969 + 3 ^ 40 * 3923047 * 2
def baseEnd_3923047 : Nat := 1342939160786011862847161

theorem tailTrace_3923047 : CollatzResearch.WordTrace tailWord_3923047 prefixEnd_3923047 1342939160786011862847161 := by
  unfold tailWord_3923047
  simp only [CollatzResearch.WordTrace]
  refine ⟨143085279018478196931039395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95390186012318797954026263 143085279018478196931039395)
  ·
    refine ⟨214627918527717295396559093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143085279018478196931039395 214627918527717295396559093)
    ·
      refine ⟨20121367361973496443427415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214627918527717295396559093 20121367361973496443427415)
      ·
        refine ⟨30182051042960244665141123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20121367361973496443427415 30182051042960244665141123)
        ·
          refine ⟨45273076564440366997711685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30182051042960244665141123 45273076564440366997711685)
          ·
            refine ⟨8488701855832568812070941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45273076564440366997711685 8488701855832568812070941)
            ·
              refine ⟨3183263195937213304526603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8488701855832568812070941 3183263195937213304526603)
              ·
                refine ⟨4774894793905819956789905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3183263195937213304526603 4774894793905819956789905)
                ·
                  refine ⟨3581171095429364967592429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4774894793905819956789905 3581171095429364967592429)
                  ·
                    refine ⟨1342939160786011862847161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3581171095429364967592429 1342939160786011862847161)
                    ·
                      rfl

theorem cell22_3923047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_3923047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923047 prefixEnd_3923047 := by exact prefixLift 3923047
  have htrace : WordTrace (prefixWord ++ tailWord_3923047) baseStart_3923047 baseEnd_3923047 := by
    simpa [prefixWord, tailWord_3923047, baseEnd_3923047] using wordTrace_append hprefix tailTrace_3923047
  have hstable : (prefixWord ++ tailWord_3923047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923047).length < 2 ^ (prefixWord ++ tailWord_3923047).sum := by decide
  have hdescent : baseEnd_3923047 < baseStart_3923047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923180 : List Nat := [2, 2, 1, 1, 2, 4, 3, 1, 2, 4]
def baseStart_3923180 : Nat := 118140960795 + 3923180 * 2 ^ 59
def prefixEnd_3923180 : Nat := 4983230072969 + 3 ^ 40 * 3923180 * 2
def baseEnd_3923180 : Nat := 1342984689404043849271753

theorem tailTrace_3923180 : CollatzResearch.WordTrace tailWord_3923180 prefixEnd_3923180 1342984689404043849271753 := by
  unfold tailWord_3923180
  simp only [CollatzResearch.WordTrace]
  refine ⟨71545064963498180322815497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95393419951330907097087329 71545064963498180322815497)
  ·
    refine ⟨53658798722623635242111623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71545064963498180322815497 53658798722623635242111623)
    ·
      refine ⟨80488198083935452863167435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53658798722623635242111623 80488198083935452863167435)
      ·
        refine ⟨120732297125903179294751153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80488198083935452863167435 120732297125903179294751153)
        ·
          refine ⟨90549222844427384471063365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120732297125903179294751153 90549222844427384471063365)
          ·
            refine ⟨16977979283330134588324381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90549222844427384471063365 16977979283330134588324381)
            ·
              refine ⟨6366742231248800470621643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16977979283330134588324381 6366742231248800470621643)
              ·
                refine ⟨9550113346873200705932465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6366742231248800470621643 9550113346873200705932465)
                ·
                  refine ⟨7162585010154900529449349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9550113346873200705932465 7162585010154900529449349)
                  ·
                    refine ⟨1342984689404043849271753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7162585010154900529449349 1342984689404043849271753)
                    ·
                      rfl

theorem cell22_3923180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_3923180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923180 prefixEnd_3923180 := by exact prefixLift 3923180
  have htrace : WordTrace (prefixWord ++ tailWord_3923180) baseStart_3923180 baseEnd_3923180 := by
    simpa [prefixWord, tailWord_3923180, baseEnd_3923180] using wordTrace_append hprefix tailTrace_3923180
  have hstable : (prefixWord ++ tailWord_3923180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923180).length < 2 ^ (prefixWord ++ tailWord_3923180).sum := by decide
  have hdescent : baseEnd_3923180 < baseStart_3923180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923186 : List Nat := [3, 2, 1, 3, 4, 1, 2, 1, 1, 4]
def baseStart_3923186 : Nat := 118140960795 + 3923186 * 2 ^ 59
def prefixEnd_3923186 : Nat := 4983230072969 + 3 ^ 40 * 3923186 * 2
def baseEnd_3923186 : Nat := 1342986743326661833621735

theorem tailTrace_3923186 : CollatzResearch.WordTrace tailWord_3923186 prefixEnd_3923186 1342986743326661833621735 := by
  unfold tailWord_3923186
  simp only [CollatzResearch.WordTrace]
  refine ⟨35772587191243655917587353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95393565843316415780232941 35772587191243655917587353)
  ·
    refine ⟨26829440393432741938190515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35772587191243655917587353 26829440393432741938190515)
    ·
      refine ⟨40244160590149112907285773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26829440393432741938190515 40244160590149112907285773)
      ·
        refine ⟨15091560221305917340232165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40244160590149112907285773 15091560221305917340232165)
        ·
          refine ⟨2829667541494859501293531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15091560221305917340232165 2829667541494859501293531)
          ·
            refine ⟨4244501312242289251940297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829667541494859501293531 4244501312242289251940297)
            ·
              refine ⟨3183375984181716938955223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4244501312242289251940297 3183375984181716938955223)
              ·
                refine ⟨4775063976272575408432835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3183375984181716938955223 4775063976272575408432835)
                ·
                  refine ⟨7162595964408863112649253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4775063976272575408432835 7162595964408863112649253)
                  ·
                    refine ⟨1342986743326661833621735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7162595964408863112649253 1342986743326661833621735)
                    ·
                      rfl

theorem cell22_3923186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_3923186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923186 prefixEnd_3923186 := by exact prefixLift 3923186
  have htrace : WordTrace (prefixWord ++ tailWord_3923186) baseStart_3923186 baseEnd_3923186 := by
    simpa [prefixWord, tailWord_3923186, baseEnd_3923186] using wordTrace_append hprefix tailTrace_3923186
  have hstable : (prefixWord ++ tailWord_3923186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923186).length < 2 ^ (prefixWord ++ tailWord_3923186).sum := by decide
  have hdescent : baseEnd_3923186 < baseStart_3923186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923240 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 7]
def baseStart_3923240 : Nat := 118140960795 + 3923240 * 2 ^ 59
def prefixEnd_3923240 : Nat := 4983230072969 + 3 ^ 40 * 3923240 * 2
def baseEnd_3923240 : Nat := 447668409543407897590523

theorem tailTrace_3923240 : CollatzResearch.WordTrace tailWord_3923240 prefixEnd_3923240 447668409543407897590523 := by
  unfold tailWord_3923240
  simp only [CollatzResearch.WordTrace]
  refine ⟨71546159153389495446407587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95394878871185993928543449 71546159153389495446407587)
  ·
    refine ⟨107319238730084243169611381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71546159153389495446407587 107319238730084243169611381)
    ·
      refine ⟨10061178630945397797151067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107319238730084243169611381 10061178630945397797151067)
      ·
        refine ⟨15091767946418096695726601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10061178630945397797151067 15091767946418096695726601)
        ·
          refine ⟨11318825959813572521794951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15091767946418096695726601 11318825959813572521794951)
          ·
            refine ⟨16978238939720358782692427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11318825959813572521794951 16978238939720358782692427)
            ·
              refine ⟨25467358409580538174038641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16978238939720358782692427 25467358409580538174038641)
              ·
                refine ⟨19100518807185403630528981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25467358409580538174038641 19100518807185403630528981)
                ·
                  refine ⟨447668409543407897590523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19100518807185403630528981 447668409543407897590523)
                  ·
                    rfl

theorem cell22_3923240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 7].length) (baseStart_3923240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923240 prefixEnd_3923240 := by exact prefixLift 3923240
  have htrace : WordTrace (prefixWord ++ tailWord_3923240) baseStart_3923240 baseEnd_3923240 := by
    simpa [prefixWord, tailWord_3923240, baseEnd_3923240] using wordTrace_append hprefix tailTrace_3923240
  have hstable : (prefixWord ++ tailWord_3923240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923240).length < 2 ^ (prefixWord ++ tailWord_3923240).sum := by decide
  have hdescent : baseEnd_3923240 < baseStart_3923240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923261 : List Nat := [1, 4, 1, 5, 1, 2, 1, 1, 3, 3]
def baseStart_3923261 : Nat := 118140960795 + 3923261 * 2 ^ 59
def prefixEnd_3923261 : Nat := 4983230072969 + 3 ^ 40 * 3923261 * 2
def baseEnd_3923261 : Nat := 1343012417359386637996505

theorem tailTrace_3923261 : CollatzResearch.WordTrace tailWord_3923261 prefixEnd_3923261 1343012417359386637996505 := by
  unfold tailWord_3923261
  simp only [CollatzResearch.WordTrace]
  refine ⟨143093084239702911479329637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95395389493135274319553091 143093084239702911479329637)
  ·
    refine ⟨26829953294944295902374307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143093084239702911479329637 26829953294944295902374307)
    ·
      refine ⟨40244929942416443853561461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26829953294944295902374307 40244929942416443853561461)
      ·
        refine ⟨3772962182101541611271387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40244929942416443853561461 3772962182101541611271387)
        ·
          refine ⟨5659443273152312416907081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3772962182101541611271387 5659443273152312416907081)
          ·
            refine ⟨4244582454864234312680311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5659443273152312416907081 4244582454864234312680311)
            ·
              refine ⟨6366873682296351469020467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4244582454864234312680311 6366873682296351469020467)
              ·
                refine ⟨9550310523444527203530701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6366873682296351469020467 9550310523444527203530701)
                ·
                  refine ⟨3581366446291697701324013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9550310523444527203530701 3581366446291697701324013)
                  ·
                    refine ⟨1343012417359386637996505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3581366446291697701324013 1343012417359386637996505)
                    ·
                      rfl

theorem cell22_3923261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_3923261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923261 prefixEnd_3923261 := by exact prefixLift 3923261
  have htrace : WordTrace (prefixWord ++ tailWord_3923261) baseStart_3923261 baseEnd_3923261 := by
    simpa [prefixWord, tailWord_3923261, baseEnd_3923261] using wordTrace_append hprefix tailTrace_3923261
  have hstable : (prefixWord ++ tailWord_3923261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923261).length < 2 ^ (prefixWord ++ tailWord_3923261).sum := by decide
  have hdescent : baseEnd_3923261 < baseStart_3923261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923287 : List Nat := [1, 1, 3, 2, 3, 2, 3, 2, 1, 4]
def baseStart_3923287 : Nat := 118140960795 + 3923287 * 2 ^ 59
def prefixEnd_3923287 : Nat := 4983230072969 + 3 ^ 40 * 3923287 * 2
def baseEnd_3923287 : Nat := 1343021317690731236846425

theorem tailTrace_3923287 : CollatzResearch.WordTrace tailWord_3923287 prefixEnd_3923287 1343021317690731236846425 := by
  unfold tailWord_3923287
  simp only [CollatzResearch.WordTrace]
  refine ⟨143094032537608717919776115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95396021691739145279850743 143094032537608717919776115)
  ·
    refine ⟨214641048806413076879664173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143094032537608717919776115 214641048806413076879664173)
    ·
      refine ⟨80490393302404903829874065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214641048806413076879664173 80490393302404903829874065)
      ·
        refine ⟨60367794976803677872405549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80490393302404903829874065 60367794976803677872405549)
        ·
          refine ⟨22637923116301379202152081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60367794976803677872405549 22637923116301379202152081)
          ·
            refine ⟨16978442337226034401614061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22637923116301379202152081 16978442337226034401614061)
            ·
              refine ⟨6366915876459762900605273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16978442337226034401614061 6366915876459762900605273)
              ·
                refine ⟨4775186907344822175453955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6366915876459762900605273 4775186907344822175453955)
                ·
                  refine ⟨7162780361017233263180933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4775186907344822175453955 7162780361017233263180933)
                  ·
                    refine ⟨1343021317690731236846425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7162780361017233263180933 1343021317690731236846425)
                    ·
                      rfl

theorem cell22_3923287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_3923287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923287 prefixEnd_3923287 := by exact prefixLift 3923287
  have htrace : WordTrace (prefixWord ++ tailWord_3923287) baseStart_3923287 baseEnd_3923287 := by
    simpa [prefixWord, tailWord_3923287, baseEnd_3923287] using wordTrace_append hprefix tailTrace_3923287
  have hstable : (prefixWord ++ tailWord_3923287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923287).length < 2 ^ (prefixWord ++ tailWord_3923287).sum := by decide
  have hdescent : baseEnd_3923287 < baseStart_3923287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923300 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_3923300 : Nat := 118140960795 + 3923300 * 2 ^ 59
def prefixEnd_3923300 : Nat := 4983230072969 + 3 ^ 40 * 3923300 * 2
def baseEnd_3923300 : Nat := 1343025767856403536271385

theorem tailTrace_3923300 : CollatzResearch.WordTrace tailWord_3923300 prefixEnd_3923300 1343025767856403536271385 := by
  unfold tailWord_3923300
  simp only [CollatzResearch.WordTrace]
  refine ⟨71547253343280810569999677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95396337791041080759999569 71547253343280810569999677)
  ·
    refine ⟨26830220003730303963749879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71547253343280810569999677 26830220003730303963749879)
    ·
      refine ⟨40245330005595455945624819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26830220003730303963749879 40245330005595455945624819)
      ·
        refine ⟨60367995008393183918437229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40245330005595455945624819 60367995008393183918437229)
        ·
          refine ⟨22637998128147443969413961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60367995008393183918437229 22637998128147443969413961)
          ·
            refine ⟨16978498596110582977060471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22637998128147443969413961 16978498596110582977060471)
            ·
              refine ⟨25467747894165874465590707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16978498596110582977060471 25467747894165874465590707)
              ·
                refine ⟨38201621841248811698386061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25467747894165874465590707 38201621841248811698386061)
                ·
                  refine ⟨14325608190468304386894773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38201621841248811698386061 14325608190468304386894773)
                  ·
                    refine ⟨1343025767856403536271385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14325608190468304386894773 1343025767856403536271385)
                    ·
                      rfl

theorem cell22_3923300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_3923300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923300 prefixEnd_3923300 := by exact prefixLift 3923300
  have htrace : WordTrace (prefixWord ++ tailWord_3923300) baseStart_3923300 baseEnd_3923300 := by
    simpa [prefixWord, tailWord_3923300, baseEnd_3923300] using wordTrace_append hprefix tailTrace_3923300
  have hstable : (prefixWord ++ tailWord_3923300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923300).length < 2 ^ (prefixWord ++ tailWord_3923300).sum := by decide
  have hdescent : baseEnd_3923300 < baseStart_3923300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923368 : List Nat := [2, 1, 6, 1, 2, 2, 1, 2, 2, 3]
def baseStart_3923368 : Nat := 118140960795 + 3923368 * 2 ^ 59
def prefixEnd_3923368 : Nat := 4983230072969 + 3 ^ 40 * 3923368 * 2
def baseEnd_3923368 : Nat := 1343049045646074025571177

theorem tailTrace_3923368 : CollatzResearch.WordTrace tailWord_3923368 prefixEnd_3923368 1343049045646074025571177 := by
  unfold tailWord_3923368
  simp only [CollatzResearch.WordTrace]
  refine ⟨71548493425157634376737379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95397991233543512502316505 71548493425157634376737379)
  ·
    refine ⟨107322740137736451565106069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71548493425157634376737379 107322740137736451565106069)
    ·
      refine ⟨5030753443956396167114347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107322740137736451565106069 5030753443956396167114347)
      ·
        refine ⟨7546130165934594250671521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5030753443956396167114347 7546130165934594250671521)
        ·
          refine ⟨5659597624450945688003641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7546130165934594250671521 5659597624450945688003641)
          ·
            refine ⟨4244698218338209266002731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5659597624450945688003641 4244698218338209266002731)
            ·
              refine ⟨6367047327507313899004097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4244698218338209266002731 6367047327507313899004097)
              ·
                refine ⟨4775285495630485424253073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6367047327507313899004097 4775285495630485424253073)
                ·
                  refine ⟨3581464121722864068189805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4775285495630485424253073 3581464121722864068189805)
                  ·
                    refine ⟨1343049045646074025571177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3581464121722864068189805 1343049045646074025571177)
                    ·
                      rfl

theorem cell22_3923368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_3923368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923368 prefixEnd_3923368 := by exact prefixLift 3923368
  have htrace : WordTrace (prefixWord ++ tailWord_3923368) baseStart_3923368 baseEnd_3923368 := by
    simpa [prefixWord, tailWord_3923368, baseEnd_3923368] using wordTrace_append hprefix tailTrace_3923368
  have hstable : (prefixWord ++ tailWord_3923368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923368).length < 2 ^ (prefixWord ++ tailWord_3923368).sum := by decide
  have hdescent : baseEnd_3923368 < baseStart_3923368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923435 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 5, 5]
def baseStart_3923435 : Nat := 118140960795 + 3923435 * 2 ^ 59
def prefixEnd_3923435 : Nat := 4983230072969 + 3 ^ 40 * 3923435 * 2
def baseEnd_3923435 : Nat := 1343071981115308184145971

theorem tailTrace_3923435 : CollatzResearch.WordTrace tailWord_3923435 prefixEnd_3923435 1343071981115308184145971 := by
  unfold tailWord_3923435
  simp only [CollatzResearch.WordTrace]
  refine ⟨143099430541072539196163759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95399620360715026130775839 143099430541072539196163759)
  ·
    refine ⟨214649145811608808794245639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143099430541072539196163759 214649145811608808794245639)
    ·
      refine ⟨321973718717413213191368459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214649145811608808794245639 321973718717413213191368459)
      ·
        refine ⟨482960578076119819787052689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321973718717413213191368459 482960578076119819787052689)
        ·
          refine ⟨362220433557089864840289517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482960578076119819787052689 362220433557089864840289517)
          ·
            refine ⟨135832662583908699315108569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 362220433557089864840289517 135832662583908699315108569)
            ·
              refine ⟨101874496937931524486331427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135832662583908699315108569 101874496937931524486331427)
              ·
                refine ⟨152811745406897286729497141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101874496937931524486331427 152811745406897286729497141)
                ·
                  refine ⟨14326101131896620630890357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152811745406897286729497141 14326101131896620630890357)
                  ·
                    refine ⟨1343071981115308184145971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14326101131896620630890357 1343071981115308184145971)
                    ·
                      rfl

theorem cell22_3923435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 5].length) (baseStart_3923435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923435 prefixEnd_3923435 := by exact prefixLift 3923435
  have htrace : WordTrace (prefixWord ++ tailWord_3923435) baseStart_3923435 baseEnd_3923435 := by
    simpa [prefixWord, tailWord_3923435, baseEnd_3923435] using wordTrace_append hprefix tailTrace_3923435
  have hstable : (prefixWord ++ tailWord_3923435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923435).length < 2 ^ (prefixWord ++ tailWord_3923435).sum := by decide
  have hdescent : baseEnd_3923435 < baseStart_3923435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923465 : List Nat := [1, 2, 1, 1, 3, 1, 3, 10]
def baseStart_3923465 : Nat := 118140960795 + 3923465 * 2 ^ 59
def prefixEnd_3923465 : Nat := 4983230072969 + 3 ^ 40 * 3923465 * 2
def baseEnd_3923465 : Nat := 149231361192044233988431

theorem tailTrace_3923465 : CollatzResearch.WordTrace tailWord_3923465 prefixEnd_3923465 149231361192044233988431 := by
  unfold tailWord_3923465
  simp only [CollatzResearch.WordTrace]
  refine ⟨143100524730963854319755849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95400349820642569546503899 143100524730963854319755849)
  ·
    refine ⟨107325393548222890739816887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143100524730963854319755849 107325393548222890739816887)
    ·
      refine ⟨160988090322334336109725331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107325393548222890739816887 160988090322334336109725331)
      ·
        refine ⟨241482135483501504164587997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160988090322334336109725331 241482135483501504164587997)
        ·
          refine ⟨90555800806313064061720499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241482135483501504164587997 90555800806313064061720499)
          ·
            refine ⟨135833701209469596092580749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90555800806313064061720499 135833701209469596092580749)
            ·
              refine ⟨50937637953551098534717781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135833701209469596092580749 50937637953551098534717781)
              ·
                refine ⟨149231361192044233988431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50937637953551098534717781 149231361192044233988431)
                ·
                  rfl

theorem cell22_3923465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 10].length) (baseStart_3923465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923465 prefixEnd_3923465 := by exact prefixLift 3923465
  have htrace : WordTrace (prefixWord ++ tailWord_3923465) baseStart_3923465 baseEnd_3923465 := by
    simpa [prefixWord, tailWord_3923465, baseEnd_3923465] using wordTrace_append hprefix tailTrace_3923465
  have hstable : (prefixWord ++ tailWord_3923465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923465).length < 2 ^ (prefixWord ++ tailWord_3923465).sum := by decide
  have hdescent : baseEnd_3923465 < baseStart_3923465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923488 : List Nat := [2, 1, 1, 6, 1, 3, 2, 2, 4]
def baseStart_3923488 : Nat := 118140960795 + 3923488 * 2 ^ 59
def prefixEnd_3923488 : Nat := 4983230072969 + 3 ^ 40 * 3923488 * 2
def baseEnd_3923488 : Nat := 447696708032811237523603

theorem tailTrace_3923488 : CollatzResearch.WordTrace tailWord_3923488 prefixEnd_3923488 447696708032811237523603 := by
  unfold tailWord_3923488
  simp only [CollatzResearch.WordTrace]
  refine ⟨71550681804940264623921559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95400909073253686165228745 71550681804940264623921559)
  ·
    refine ⟨107326022707410396935882339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71550681804940264623921559 107326022707410396935882339)
    ·
      refine ⟨160989034061115595403823509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107326022707410396935882339 160989034061115595403823509)
      ·
        refine ⟨7546360971614793534554227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 160989034061115595403823509 7546360971614793534554227)
        ·
          refine ⟨11319541457422190301831341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7546360971614793534554227 11319541457422190301831341)
          ·
            refine ⟨4244828046533321363186753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11319541457422190301831341 4244828046533321363186753)
            ·
              refine ⟨3183621034899991022390065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4244828046533321363186753 3183621034899991022390065)
              ·
                refine ⟨2387715776174993266792549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3183621034899991022390065 2387715776174993266792549)
                ·
                  refine ⟨447696708032811237523603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2387715776174993266792549 447696708032811237523603)
                  ·
                    rfl

theorem cell22_3923488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 4].length) (baseStart_3923488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923488 prefixEnd_3923488 := by exact prefixLift 3923488
  have htrace : WordTrace (prefixWord ++ tailWord_3923488) baseStart_3923488 baseEnd_3923488 := by
    simpa [prefixWord, tailWord_3923488, baseEnd_3923488] using wordTrace_append hprefix tailTrace_3923488
  have hstable : (prefixWord ++ tailWord_3923488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923488).length < 2 ^ (prefixWord ++ tailWord_3923488).sum := by decide
  have hdescent : baseEnd_3923488 < baseStart_3923488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923514 : List Nat := [3, 1, 1, 1, 3, 2, 3, 2, 3, 3]
def baseStart_3923514 : Nat := 118140960795 + 3923514 * 2 ^ 59
def prefixEnd_3923514 : Nat := 4983230072969 + 3 ^ 40 * 3923514 * 2
def baseEnd_3923514 : Nat := 1343099024429778311420729

theorem tailTrace_3923514 : CollatzResearch.WordTrace tailWord_3923514 prefixEnd_3923514 1343099024429778311420729 := by
  unfold tailWord_3923514
  simp only [CollatzResearch.WordTrace]
  refine ⟨35775577976946583922072399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95401541271857557125526397 35775577976946583922072399)
  ·
    refine ⟨53663366965419875883108599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35775577976946583922072399 53663366965419875883108599)
    ·
      refine ⟨80495050448129813824662899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53663366965419875883108599 80495050448129813824662899)
      ·
        refine ⟨120742575672194720736994349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80495050448129813824662899 120742575672194720736994349)
        ·
          refine ⟨45278465877073020276372881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120742575672194720736994349 45278465877073020276372881)
          ·
            refine ⟨33958849407804765207279661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45278465877073020276372881 33958849407804765207279661)
            ·
              refine ⟨12734568527926786952729873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33958849407804765207279661 12734568527926786952729873)
              ·
                refine ⟨9550926395945090214547405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12734568527926786952729873 9550926395945090214547405)
                ·
                  refine ⟨3581597398479408830455277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9550926395945090214547405 3581597398479408830455277)
                  ·
                    refine ⟨1343099024429778311420729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3581597398479408830455277 1343099024429778311420729)
                    ·
                      rfl

theorem cell22_3923514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_3923514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923514 prefixEnd_3923514 := by exact prefixLift 3923514
  have htrace : WordTrace (prefixWord ++ tailWord_3923514) baseStart_3923514 baseEnd_3923514 := by
    simpa [prefixWord, tailWord_3923514, baseEnd_3923514] using wordTrace_append hprefix tailTrace_3923514
  have hstable : (prefixWord ++ tailWord_3923514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923514).length < 2 ^ (prefixWord ++ tailWord_3923514).sum := by decide
  have hdescent : baseEnd_3923514 < baseStart_3923514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923548 : List Nat := [2, 2, 4, 1, 2, 1, 2, 4, 1, 3]
def baseStart_3923548 : Nat := 118140960795 + 3923548 * 2 ^ 59
def prefixEnd_3923548 : Nat := 4983230072969 + 3 ^ 40 * 3923548 * 2
def baseEnd_3923548 : Nat := 1343110663324613556070625

theorem tailTrace_3923548 : CollatzResearch.WordTrace tailWord_3923548 prefixEnd_3923548 1343110663324613556070625 := by
  unfold tailWord_3923548
  simp only [CollatzResearch.WordTrace]
  refine ⟨71551775994831579747513649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95402367993108772996684865 71551775994831579747513649)
  ·
    refine ⟨53663831996123684810635237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71551775994831579747513649 53663831996123684810635237)
    ·
      refine ⟨10061968499273190901994107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53663831996123684810635237 10061968499273190901994107)
      ·
        refine ⟨15092952748909786352991161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10061968499273190901994107 15092952748909786352991161)
        ·
          refine ⟨11319714561682339764743371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15092952748909786352991161 11319714561682339764743371)
          ·
            refine ⟨16979571842523509647115057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11319714561682339764743371 16979571842523509647115057)
            ·
              refine ⟨12734678881892632235336293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16979571842523509647115057 12734678881892632235336293)
              ·
                refine ⟨2387752290354868544125555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12734678881892632235336293 2387752290354868544125555)
                ·
                  refine ⟨3581628435532302816188333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387752290354868544125555 3581628435532302816188333)
                  ·
                    refine ⟨1343110663324613556070625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3581628435532302816188333 1343110663324613556070625)
                    ·
                      rfl

theorem cell22_3923548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_3923548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923548 prefixEnd_3923548 := by exact prefixLift 3923548
  have htrace : WordTrace (prefixWord ++ tailWord_3923548) baseStart_3923548 baseEnd_3923548 := by
    simpa [prefixWord, tailWord_3923548, baseEnd_3923548] using wordTrace_append hprefix tailTrace_3923548
  have hstable : (prefixWord ++ tailWord_3923548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923548).length < 2 ^ (prefixWord ++ tailWord_3923548).sum := by decide
  have hdescent : baseEnd_3923548 < baseStart_3923548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923587 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 3, 5]
def baseStart_3923587 : Nat := 118140960795 + 3923587 * 2 ^ 59
def prefixEnd_3923587 : Nat := 4983230072969 + 3 ^ 40 * 3923587 * 2
def baseEnd_3923587 : Nat := 1343124013821630454345505

theorem tailTrace_3923587 : CollatzResearch.WordTrace tailWord_3923587 prefixEnd_3923587 1343124013821630454345505 := by
  unfold tailWord_3923587
  simp only [CollatzResearch.WordTrace]
  refine ⟨143104974436521869155697015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95403316291014579437131343 143104974436521869155697015)
  ·
    refine ⟨214657461654782803733545523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143104974436521869155697015 214657461654782803733545523)
    ·
      refine ⟨321986192482174205600318285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214657461654782803733545523 321986192482174205600318285)
      ·
        refine ⟨120744822180815327100119357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321986192482174205600318285 120744822180815327100119357)
        ·
          refine ⟨45279308317805747662544759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120744822180815327100119357 45279308317805747662544759)
          ·
            refine ⟨67918962476708621493817139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45279308317805747662544759 67918962476708621493817139)
            ·
              refine ⟨101878443715062932240725709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67918962476708621493817139 101878443715062932240725709)
              ·
                refine ⟨38204416393148599590272141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101878443715062932240725709 38204416393148599590272141)
                ·
                  refine ⟨14326656147430724846352053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38204416393148599590272141 14326656147430724846352053)
                  ·
                    refine ⟨1343124013821630454345505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14326656147430724846352053 1343124013821630454345505)
                    ·
                      rfl

theorem cell22_3923587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 5].length) (baseStart_3923587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923587 prefixEnd_3923587 := by exact prefixLift 3923587
  have htrace : WordTrace (prefixWord ++ tailWord_3923587) baseStart_3923587 baseEnd_3923587 := by
    simpa [prefixWord, tailWord_3923587, baseEnd_3923587] using wordTrace_append hprefix tailTrace_3923587
  have hstable : (prefixWord ++ tailWord_3923587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923587).length < 2 ^ (prefixWord ++ tailWord_3923587).sum := by decide
  have hdescent : baseEnd_3923587 < baseStart_3923587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923632 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 2, 7]
def baseStart_3923632 : Nat := 118140960795 + 3923632 * 2 ^ 59
def prefixEnd_3923632 : Nat := 4983230072969 + 3 ^ 40 * 3923632 * 2
def baseEnd_3923632 : Nat := 1343139418241265336970367

theorem tailTrace_3923632 : CollatzResearch.WordTrace tailWord_3923632 prefixEnd_3923632 1343139418241265336970367 := by
  unfold tailWord_3923632
  simp only [CollatzResearch.WordTrace]
  refine ⟨71553307860679420920542575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95404410480905894560723433 71553307860679420920542575)
  ·
    refine ⟨107329961791019131380813863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71553307860679420920542575 107329961791019131380813863)
    ·
      refine ⟨160994942686528697071220795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107329961791019131380813863 160994942686528697071220795)
      ·
        refine ⟨241492414029793045606831193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160994942686528697071220795 241492414029793045606831193)
        ·
          refine ⟨181119310522344784205123395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241492414029793045606831193 181119310522344784205123395)
          ·
            refine ⟨271678965783517176307685093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181119310522344784205123395 271678965783517176307685093)
            ·
              refine ⟨50939806084409470557690955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 271678965783517176307685093 50939806084409470557690955)
              ·
                refine ⟨76409709126614205836536433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50939806084409470557690955 76409709126614205836536433)
                ·
                  refine ⟨57307281844960654377402325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76409709126614205836536433 57307281844960654377402325)
                  ·
                    refine ⟨1343139418241265336970367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57307281844960654377402325 1343139418241265336970367)
                    ·
                      rfl

theorem cell22_3923632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_3923632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923632 prefixEnd_3923632 := by exact prefixLift 3923632
  have htrace : WordTrace (prefixWord ++ tailWord_3923632) baseStart_3923632 baseEnd_3923632 := by
    simpa [prefixWord, tailWord_3923632, baseEnd_3923632] using wordTrace_append hprefix tailTrace_3923632
  have hstable : (prefixWord ++ tailWord_3923632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923632).length < 2 ^ (prefixWord ++ tailWord_3923632).sum := by decide
  have hdescent : baseEnd_3923632 < baseStart_3923632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923638 : List Nat := [5, 1, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_3923638 : Nat := 118140960795 + 3923638 * 2 ^ 59
def prefixEnd_3923638 : Nat := 4983230072969 + 3 ^ 40 * 3923638 * 2
def baseEnd_3923638 : Nat := 1343141472163883321320349

theorem tailTrace_3923638 : CollatzResearch.WordTrace tailWord_3923638 prefixEnd_3923638 1343141472163883321320349 := by
  unfold tailWord_3923638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8944177159958569054112723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95404556372891403243869045 8944177159958569054112723)
  ·
    refine ⟨13416265739937853581169085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8944177159958569054112723 13416265739937853581169085)
    ·
      refine ⟨5031099652476695092938407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13416265739937853581169085 5031099652476695092938407)
      ·
        refine ⟨7546649478715042639407611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5031099652476695092938407 7546649478715042639407611)
        ·
          refine ⟨11319974218072563959111417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7546649478715042639407611 11319974218072563959111417)
          ·
            refine ⟨8489980663554422969333563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11319974218072563959111417 8489980663554422969333563)
            ·
              refine ⟨12734970995331634454000345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8489980663554422969333563 12734970995331634454000345)
              ·
                refine ⟨9551228246498725840500259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12734970995331634454000345 9551228246498725840500259)
                ·
                  refine ⟨14326842369748088760750389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9551228246498725840500259 14326842369748088760750389)
                  ·
                    refine ⟨1343141472163883321320349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14326842369748088760750389 1343141472163883321320349)
                    ·
                      rfl

theorem cell22_3923638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_3923638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923638 prefixEnd_3923638 := by exact prefixLift 3923638
  have htrace : WordTrace (prefixWord ++ tailWord_3923638) baseStart_3923638 baseEnd_3923638 := by
    simpa [prefixWord, tailWord_3923638, baseEnd_3923638] using wordTrace_append hprefix tailTrace_3923638
  have hstable : (prefixWord ++ tailWord_3923638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923638).length < 2 ^ (prefixWord ++ tailWord_3923638).sum := by decide
  have hdescent : baseEnd_3923638 < baseStart_3923638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923679 : List Nat := [1, 1, 2, 3, 2, 2, 1, 5, 5]
def baseStart_3923679 : Nat := 118140960795 + 3923679 * 2 ^ 59
def prefixEnd_3923679 : Nat := 4983230072969 + 3 ^ 40 * 3923679 * 2
def baseEnd_3923679 : Nat := 447718502433924293681741

theorem tailTrace_3923679 : CollatzResearch.WordTrace tailWord_3923679 prefixEnd_3923679 447718502433924293681741 := by
  unfold tailWord_3923679
  simp only [CollatzResearch.WordTrace]
  refine ⟨143108329952188568868046091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95405553301459045912030727 143108329952188568868046091)
  ·
    refine ⟨214662494928282853302069137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143108329952188568868046091 214662494928282853302069137)
    ·
      refine ⟨160996871196212139976551853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214662494928282853302069137 160996871196212139976551853)
      ·
        refine ⟨60373826698579552491206945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160996871196212139976551853 60373826698579552491206945)
        ·
          refine ⟨45280370023934664368405209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60373826698579552491206945 45280370023934664368405209)
          ·
            refine ⟨33960277517950998276303907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45280370023934664368405209 33960277517950998276303907)
            ·
              refine ⟨50940416276926497414455861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33960277517950998276303907 50940416276926497414455861)
              ·
                refine ⟨4775664025961859132605237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50940416276926497414455861 4775664025961859132605237)
                ·
                  refine ⟨447718502433924293681741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4775664025961859132605237 447718502433924293681741)
                  ·
                    rfl

theorem cell22_3923679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 5].length) (baseStart_3923679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923679 prefixEnd_3923679 := by exact prefixLift 3923679
  have htrace : WordTrace (prefixWord ++ tailWord_3923679) baseStart_3923679 baseEnd_3923679 := by
    simpa [prefixWord, tailWord_3923679, baseEnd_3923679] using wordTrace_append hprefix tailTrace_3923679
  have hstable : (prefixWord ++ tailWord_3923679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923679).length < 2 ^ (prefixWord ++ tailWord_3923679).sum := by decide
  have hdescent : baseEnd_3923679 < baseStart_3923679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923683 : List Nat := [1, 1, 1, 7, 2, 1, 1, 2, 3, 3]
def baseStart_3923683 : Nat := 118140960795 + 3923683 * 2 ^ 59
def prefixEnd_3923683 : Nat := 4983230072969 + 3 ^ 40 * 3923683 * 2
def baseEnd_3923683 : Nat := 1343156876583518203945211

theorem tailTrace_3923683 : CollatzResearch.WordTrace tailWord_3923683 prefixEnd_3923683 1343156876583518203945211 := by
  unfold tailWord_3923683
  simp only [CollatzResearch.WordTrace]
  refine ⟨143108475844174077551191703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95405650562782718367461135 143108475844174077551191703)
  ·
    refine ⟨214662713766261116326787555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143108475844174077551191703 214662713766261116326787555)
    ·
      refine ⟨321994070649391674490181333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214662713766261116326787555 321994070649391674490181333)
      ·
        refine ⟨7546736030845117370863625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 321994070649391674490181333 7546736030845117370863625)
        ·
          refine ⟨5660052023133838028147719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7546736030845117370863625 5660052023133838028147719)
          ·
            refine ⟨8490078034700757042221579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5660052023133838028147719 8490078034700757042221579)
            ·
              refine ⟨12735117052051135563332369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8490078034700757042221579 12735117052051135563332369)
              ·
                refine ⟨9551337789038351672499277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12735117052051135563332369 9551337789038351672499277)
                ·
                  refine ⟨3581751670889381877187229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9551337789038351672499277 3581751670889381877187229)
                  ·
                    refine ⟨1343156876583518203945211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3581751670889381877187229 1343156876583518203945211)
                    ·
                      rfl

theorem cell22_3923683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 3].length) (baseStart_3923683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923683 prefixEnd_3923683 := by exact prefixLift 3923683
  have htrace : WordTrace (prefixWord ++ tailWord_3923683) baseStart_3923683 baseEnd_3923683 := by
    simpa [prefixWord, tailWord_3923683, baseEnd_3923683] using wordTrace_append hprefix tailTrace_3923683
  have hstable : (prefixWord ++ tailWord_3923683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923683).length < 2 ^ (prefixWord ++ tailWord_3923683).sum := by decide
  have hdescent : baseEnd_3923683 < baseStart_3923683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923694 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_3923694 : Nat := 118140960795 + 3923694 * 2 ^ 59
def prefixEnd_3923694 : Nat := 4983230072969 + 3 ^ 40 * 3923694 * 2
def baseEnd_3923694 : Nat := 1343160642108317841920177

theorem tailTrace_3923694 : CollatzResearch.WordTrace tailWord_3923694 prefixEnd_3923694 1343160642108317841920177 := by
  unfold tailWord_3923694
  simp only [CollatzResearch.WordTrace]
  refine ⟨17888609630891778303730267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95405918031422817619894757 17888609630891778303730267)
  ·
    refine ⟨26832914446337667455595401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17888609630891778303730267 26832914446337667455595401)
    ·
      refine ⟨20124685834753250591696551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26832914446337667455595401 20124685834753250591696551)
      ·
        refine ⟨30187028752129875887544827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20124685834753250591696551 30187028752129875887544827)
        ·
          refine ⟨45280543128194813831317241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30187028752129875887544827 45280543128194813831317241)
          ·
            refine ⟨33960407346146110373487931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45280543128194813831317241 33960407346146110373487931)
            ·
              refine ⟨50940611019219165560231897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33960407346146110373487931 50940611019219165560231897)
              ·
                refine ⟨38205458264414374170173923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50940611019219165560231897 38205458264414374170173923)
                ·
                  refine ⟨57308187396621561255260885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38205458264414374170173923 57308187396621561255260885)
                  ·
                    refine ⟨1343160642108317841920177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57308187396621561255260885 1343160642108317841920177)
                    ·
                      rfl

theorem cell22_3923694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_3923694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923694 prefixEnd_3923694 := by exact prefixLift 3923694
  have htrace : WordTrace (prefixWord ++ tailWord_3923694) baseStart_3923694 baseEnd_3923694 := by
    simpa [prefixWord, tailWord_3923694, baseEnd_3923694] using wordTrace_append hprefix tailTrace_3923694
  have hstable : (prefixWord ++ tailWord_3923694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923694).length < 2 ^ (prefixWord ++ tailWord_3923694).sum := by decide
  have hdescent : baseEnd_3923694 < baseStart_3923694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923709 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_3923709 : Nat := 118140960795 + 3923709 * 2 ^ 59
def prefixEnd_3923709 : Nat := 4983230072969 + 3 ^ 40 * 3923709 * 2
def baseEnd_3923709 : Nat := 1343165776914862802795131

theorem tailTrace_3923709 : CollatzResearch.WordTrace tailWord_3923709 prefixEnd_3923709 1343165776914862802795131 := by
  unfold tailWord_3923709
  simp only [CollatzResearch.WordTrace]
  refine ⟨143109424142079883991638181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95406282761386589327758787 143109424142079883991638181)
  ·
    refine ⟨26833017026639978248432159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143109424142079883991638181 26833017026639978248432159)
    ·
      refine ⟨40249525539959967372648239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26833017026639978248432159 40249525539959967372648239)
      ·
        refine ⟨60374288309939951058972359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40249525539959967372648239 60374288309939951058972359)
        ·
          refine ⟨90561432464909926588458539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60374288309939951058972359 90561432464909926588458539)
          ·
            refine ⟨135842148697364889882687809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90561432464909926588458539 135842148697364889882687809)
            ·
              refine ⟨101881611523023667412015857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135842148697364889882687809 101881611523023667412015857)
              ·
                refine ⟨76411208642267750559011893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101881611523023667412015857 76411208642267750559011893)
                ·
                  refine ⟨7163550810212601614907365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76411208642267750559011893 7163550810212601614907365)
                  ·
                    refine ⟨1343165776914862802795131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7163550810212601614907365 1343165776914862802795131)
                    ·
                      rfl

theorem cell22_3923709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_3923709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923709 prefixEnd_3923709 := by exact prefixLift 3923709
  have htrace : WordTrace (prefixWord ++ tailWord_3923709) baseStart_3923709 baseEnd_3923709 := by
    simpa [prefixWord, tailWord_3923709, baseEnd_3923709] using wordTrace_append hprefix tailTrace_3923709
  have hstable : (prefixWord ++ tailWord_3923709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923709).length < 2 ^ (prefixWord ++ tailWord_3923709).sum := by decide
  have hdescent : baseEnd_3923709 < baseStart_3923709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923724 : List Nat := [2, 2, 1, 2, 2, 1, 3, 3, 6]
def baseStart_3923724 : Nat := 118140960795 + 3923724 * 2 ^ 59
def prefixEnd_3923724 : Nat := 4983230072969 + 3 ^ 40 * 3923724 * 2
def baseEnd_3923724 : Nat := 447723637240469254556695

theorem tailTrace_3923724 : CollatzResearch.WordTrace tailWord_3923724 prefixEnd_3923724 447723637240469254556695 := by
  unfold tailWord_3923724
  simp only [CollatzResearch.WordTrace]
  refine ⟨71554985618512770776717113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95406647491350361035622817 71554985618512770776717113)
  ·
    refine ⟨53666239213884578082537835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71554985618512770776717113 53666239213884578082537835)
    ·
      refine ⟨80499358820826867123806753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53666239213884578082537835 80499358820826867123806753)
      ·
        refine ⟨60374519115620150342855065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80499358820826867123806753 60374519115620150342855065)
        ·
          refine ⟨45280889336715112757141299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60374519115620150342855065 45280889336715112757141299)
          ·
            refine ⟨67921334005072669135711949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45280889336715112757141299 67921334005072669135711949)
            ·
              refine ⟨25470500251902250925891981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67921334005072669135711949 25470500251902250925891981)
              ·
                refine ⟨9551437594463344097209493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25470500251902250925891981 9551437594463344097209493)
                ·
                  refine ⟨447723637240469254556695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9551437594463344097209493 447723637240469254556695)
                  ·
                    rfl

theorem cell22_3923724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_3923724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923724 prefixEnd_3923724 := by exact prefixLift 3923724
  have htrace : WordTrace (prefixWord ++ tailWord_3923724) baseStart_3923724 baseEnd_3923724 := by
    simpa [prefixWord, tailWord_3923724, baseEnd_3923724] using wordTrace_append hprefix tailTrace_3923724
  have hstable : (prefixWord ++ tailWord_3923724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923724).length < 2 ^ (prefixWord ++ tailWord_3923724).sum := by decide
  have hdescent : baseEnd_3923724 < baseStart_3923724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923730 : List Nat := [3, 2, 4, 1, 1, 2, 3, 1, 5]
def baseStart_3923730 : Nat := 118140960795 + 3923730 * 2 ^ 59
def prefixEnd_3923730 : Nat := 4983230072969 + 3 ^ 40 * 3923730 * 2
def baseEnd_3923730 : Nat := 447724321881341916006689

theorem tailTrace_3923730 : CollatzResearch.WordTrace tailWord_3923730 prefixEnd_3923730 447724321881341916006689 := by
  unfold tailWord_3923730
  simp only [CollatzResearch.WordTrace]
  refine ⟨35777547518750951144538161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95406793383335869718768429 35777547518750951144538161)
  ·
    refine ⟨26833160639063213358403621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35777547518750951144538161 26833160639063213358403621)
    ·
      refine ⟨5031217619824352504700679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26833160639063213358403621 5031217619824352504700679)
      ·
        refine ⟨7546826429736528757051019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5031217619824352504700679 7546826429736528757051019)
        ·
          refine ⟨11320239644604793135576529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7546826429736528757051019 11320239644604793135576529)
          ·
            refine ⟨8490179733453594851682397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11320239644604793135576529 8490179733453594851682397)
            ·
              refine ⟨3183817400045098069380899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8490179733453594851682397 3183817400045098069380899)
              ·
                refine ⟨4775726100067647104071349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3183817400045098069380899 4775726100067647104071349)
                ·
                  refine ⟨447724321881341916006689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4775726100067647104071349 447724321881341916006689)
                  ·
                    rfl

theorem cell22_3923730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_3923730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923730 prefixEnd_3923730 := by exact prefixLift 3923730
  have htrace : WordTrace (prefixWord ++ tailWord_3923730) baseStart_3923730 baseEnd_3923730 := by
    simpa [prefixWord, tailWord_3923730, baseEnd_3923730] using wordTrace_append hprefix tailTrace_3923730
  have hstable : (prefixWord ++ tailWord_3923730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923730).length < 2 ^ (prefixWord ++ tailWord_3923730).sum := by decide
  have hdescent : baseEnd_3923730 < baseStart_3923730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923756 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 4, 3]
def baseStart_3923756 : Nat := 118140960795 + 3923756 * 2 ^ 59
def prefixEnd_3923756 : Nat := 4983230072969 + 3 ^ 40 * 3923756 * 2
def baseEnd_3923756 : Nat := 1343181865975370346869987

theorem tailTrace_3923756 : CollatzResearch.WordTrace tailWord_3923756 prefixEnd_3923756 1343181865975370346869987 := by
  unfold tailWord_3923756
  simp only [CollatzResearch.WordTrace]
  refine ⟨71555569186454805509299561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95407425581939740679066081 71555569186454805509299561)
  ·
    refine ⟨53666676889841104131974671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71555569186454805509299561 53666676889841104131974671)
    ·
      refine ⟨80500015334761656197962007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53666676889841104131974671 80500015334761656197962007)
      ·
        refine ⟨120750023002142484296943011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80500015334761656197962007 120750023002142484296943011)
        ·
          refine ⟨181125034503213726445414517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120750023002142484296943011 181125034503213726445414517)
          ·
            refine ⟨16980471984676286854257611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181125034503213726445414517 16980471984676286854257611)
            ·
              refine ⟨25470707977014430281386417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16980471984676286854257611 25470707977014430281386417)
              ·
                refine ⟨19103030982760822711039813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25470707977014430281386417 19103030982760822711039813)
                ·
                  refine ⟨3581818309267654258319965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19103030982760822711039813 3581818309267654258319965)
                  ·
                    refine ⟨1343181865975370346869987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3581818309267654258319965 1343181865975370346869987)
                    ·
                      rfl

theorem cell22_3923756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_3923756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923756 prefixEnd_3923756 := by exact prefixLift 3923756
  have htrace : WordTrace (prefixWord ++ tailWord_3923756) baseStart_3923756 baseEnd_3923756 := by
    simpa [prefixWord, tailWord_3923756, baseEnd_3923756] using wordTrace_append hprefix tailTrace_3923756
  have hstable : (prefixWord ++ tailWord_3923756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923756).length < 2 ^ (prefixWord ++ tailWord_3923756).sum := by decide
  have hdescent : baseEnd_3923756 < baseStart_3923756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923773 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 4, 3]
def baseStart_3923773 : Nat := 118140960795 + 3923773 * 2 ^ 59
def prefixEnd_3923773 : Nat := 4983230072969 + 3 ^ 40 * 3923773 * 2
def baseEnd_3923773 : Nat := 1343187685422787969194935

theorem tailTrace_3923773 : CollatzResearch.WordTrace tailWord_3923773 prefixEnd_3923773 1343187685422787969194935 := by
  unfold tailWord_3923773
  simp only [CollatzResearch.WordTrace]
  refine ⟨143111758413848022921967973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95407838942565348614645315 143111758413848022921967973)
  ·
    refine ⟨26833454702596504297868995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143111758413848022921967973 26833454702596504297868995)
    ·
      refine ⟨40250182053894756446803493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26833454702596504297868995 40250182053894756446803493)
      ·
        refine ⟨7546909135105266833775655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40250182053894756446803493 7546909135105266833775655)
        ·
          refine ⟨11320363702657900250663483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7546909135105266833775655 11320363702657900250663483)
          ·
            refine ⟨16980545553986850375995225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11320363702657900250663483 16980545553986850375995225)
            ·
              refine ⟨12735409165490137781996419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16980545553986850375995225 12735409165490137781996419)
              ·
                refine ⟨19103113748235206672994629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12735409165490137781996419 19103113748235206672994629)
                ·
                  refine ⟨3581833827794101251186493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19103113748235206672994629 3581833827794101251186493)
                  ·
                    refine ⟨1343187685422787969194935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3581833827794101251186493 1343187685422787969194935)
                    ·
                      rfl

theorem cell22_3923773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_3923773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923773 prefixEnd_3923773 := by exact prefixLift 3923773
  have htrace : WordTrace (prefixWord ++ tailWord_3923773) baseStart_3923773 baseEnd_3923773 := by
    simpa [prefixWord, tailWord_3923773, baseEnd_3923773] using wordTrace_append hprefix tailTrace_3923773
  have hstable : (prefixWord ++ tailWord_3923773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923773).length < 2 ^ (prefixWord ++ tailWord_3923773).sum := by decide
  have hdescent : baseEnd_3923773 < baseStart_3923773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923775 : List Nat := [1, 1, 2, 2, 6, 1, 3, 2, 4]
def baseStart_3923775 : Nat := 118140960795 + 3923775 * 2 ^ 59
def prefixEnd_3923775 : Nat := 4983230072969 + 3 ^ 40 * 3923775 * 2
def baseEnd_3923775 : Nat := 447729456687886876881643

theorem tailTrace_3923775 : CollatzResearch.WordTrace tailWord_3923775 prefixEnd_3923775 447729456687886876881643 := by
  unfold tailWord_3923775
  simp only [CollatzResearch.WordTrace]
  refine ⟨143111831359840777263540779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95407887573227184842360519 143111831359840777263540779)
  ·
    refine ⟨214667747039761165895311169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143111831359840777263540779 214667747039761165895311169)
    ·
      refine ⟨161000810279820874421483377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214667747039761165895311169 161000810279820874421483377)
      ·
        refine ⟨120750607709865655816112533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161000810279820874421483377 120750607709865655816112533)
        ·
          refine ⟨5660184736399952616380275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120750607709865655816112533 5660184736399952616380275)
          ·
            refine ⟨8490277104599928924570413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5660184736399952616380275 8490277104599928924570413)
            ·
              refine ⟨3183853914224973346713905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8490277104599928924570413 3183853914224973346713905)
              ·
                refine ⟨2387890435668730010035429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3183853914224973346713905 2387890435668730010035429)
                ·
                  refine ⟨447729456687886876881643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2387890435668730010035429 447729456687886876881643)
                  ·
                    rfl

theorem cell22_3923775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 4].length) (baseStart_3923775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923775 prefixEnd_3923775 := by exact prefixLift 3923775
  have htrace : WordTrace (prefixWord ++ tailWord_3923775) baseStart_3923775 baseEnd_3923775 := by
    simpa [prefixWord, tailWord_3923775, baseEnd_3923775] using wordTrace_append hprefix tailTrace_3923775
  have hstable : (prefixWord ++ tailWord_3923775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923775).length < 2 ^ (prefixWord ++ tailWord_3923775).sum := by decide
  have hdescent : baseEnd_3923775 < baseStart_3923775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923801 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 5, 3]
def baseStart_3923801 : Nat := 118140960795 + 3923801 * 2 ^ 59
def prefixEnd_3923801 : Nat := 4983230072969 + 3 ^ 40 * 3923801 * 2
def baseEnd_3923801 : Nat := 1343197270395005229494849

theorem tailTrace_3923801 : CollatzResearch.WordTrace tailWord_3923801 prefixEnd_3923801 1343197270395005229494849 := by
  unfold tailWord_3923801
  simp only [CollatzResearch.WordTrace]
  refine ⟨143112779657746583703987257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95408519771831055802658171 143112779657746583703987257)
  ·
    refine ⟨107334584743309937777990443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143112779657746583703987257 107334584743309937777990443)
    ·
      refine ⟨161001877114964906666985665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107334584743309937777990443 161001877114964906666985665)
      ·
        refine ⟨120751407836223680000239249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161001877114964906666985665 120751407836223680000239249)
        ·
          refine ⟨90563555877167760000179437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120751407836223680000239249 90563555877167760000179437)
          ·
            refine ⟨33961333453937910000067289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90563555877167760000179437 33961333453937910000067289)
            ·
              refine ⟨25471000090453432500050467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33961333453937910000067289 25471000090453432500050467)
              ·
                refine ⟨38206500135680148750075701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25471000090453432500050467 38206500135680148750075701)
                ·
                  refine ⟨3581859387720013945319597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38206500135680148750075701 3581859387720013945319597)
                  ·
                    refine ⟨1343197270395005229494849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3581859387720013945319597 1343197270395005229494849)
                    ·
                      rfl

theorem cell22_3923801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 3].length) (baseStart_3923801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923801 prefixEnd_3923801 := by exact prefixLift 3923801
  have htrace : WordTrace (prefixWord ++ tailWord_3923801) baseStart_3923801 baseEnd_3923801 := by
    simpa [prefixWord, tailWord_3923801, baseEnd_3923801] using wordTrace_append hprefix tailTrace_3923801
  have hstable : (prefixWord ++ tailWord_3923801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923801).length < 2 ^ (prefixWord ++ tailWord_3923801).sum := by decide
  have hdescent : baseEnd_3923801 < baseStart_3923801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923861 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 3, 4]
def baseStart_3923861 : Nat := 118140960795 + 3923861 * 2 ^ 59
def prefixEnd_3923861 : Nat := 4983230072969 + 3 ^ 40 * 3923861 * 2
def baseEnd_3923861 : Nat := 1343217809621185072994665

theorem tailTrace_3923861 : CollatzResearch.WordTrace tailWord_3923861 prefixEnd_3923861 1343217809621185072994665 := by
  unfold tailWord_3923861
  simp only [CollatzResearch.WordTrace]
  refine ⟨143114968037529213951171437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95409978691686142634114291 143114968037529213951171437)
  ·
    refine ⟨53668113014073455231689289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143114968037529213951171437 53668113014073455231689289)
    ·
      refine ⟨40251084760555091423766967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53668113014073455231689289 40251084760555091423766967)
      ·
        refine ⟨60376627140832637135650451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40251084760555091423766967 60376627140832637135650451)
        ·
          refine ⟨90564940711248955703475677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60376627140832637135650451 90564940711248955703475677)
          ·
            refine ⟨33961852766718358388803379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90564940711248955703475677 33961852766718358388803379)
            ·
              refine ⟨50942779150077537583205069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33961852766718358388803379 50942779150077537583205069)
              ·
                refine ⟨19103542181279076593701901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50942779150077537583205069 19103542181279076593701901)
                ·
                  refine ⟨7163828317979653722638213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19103542181279076593701901 7163828317979653722638213)
                  ·
                    refine ⟨1343217809621185072994665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7163828317979653722638213 1343217809621185072994665)
                    ·
                      rfl

theorem cell22_3923861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_3923861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923861 prefixEnd_3923861 := by exact prefixLift 3923861
  have htrace : WordTrace (prefixWord ++ tailWord_3923861) baseStart_3923861 baseEnd_3923861 := by
    simpa [prefixWord, tailWord_3923861, baseEnd_3923861] using wordTrace_append hprefix tailTrace_3923861
  have hstable : (prefixWord ++ tailWord_3923861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923861).length < 2 ^ (prefixWord ++ tailWord_3923861).sum := by decide
  have hdescent : baseEnd_3923861 < baseStart_3923861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923893 : List Nat := [1, 3, 3, 2, 1, 3, 2, 1, 6]
def baseStart_3923893 : Nat := 118140960795 + 3923893 * 2 ^ 59
def prefixEnd_3923893 : Nat := 4983230072969 + 3 ^ 40 * 3923893 * 2
def baseEnd_3923893 : Nat := 447742921291715885398189

theorem tailTrace_3923893 : CollatzResearch.WordTrace tailWord_3923893 prefixEnd_3923893 447742921291715885398189 := by
  unfold tailWord_3923893
  simp only [CollatzResearch.WordTrace]
  refine ⟨143116135173413283416336333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95410756782275522277557555 143116135173413283416336333)
  ·
    refine ⟨53668550690029981281126125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143116135173413283416336333 53668550690029981281126125)
    ·
      refine ⟨20125706508761242980422297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53668550690029981281126125 20125706508761242980422297)
      ·
        refine ⟨15094279881570932235316723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20125706508761242980422297 15094279881570932235316723)
        ·
          refine ⟨22641419822356398352975085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15094279881570932235316723 22641419822356398352975085)
          ·
            refine ⟨8490532433383649382365657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22641419822356398352975085 8490532433383649382365657)
            ·
              refine ⟨6367899325037737036774243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8490532433383649382365657 6367899325037737036774243)
              ·
                refine ⟨9551848987556605555161365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6367899325037737036774243 9551848987556605555161365)
                ·
                  refine ⟨447742921291715885398189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9551848987556605555161365 447742921291715885398189)
                  ·
                    rfl

theorem cell22_3923893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_3923893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923893 prefixEnd_3923893 := by exact prefixLift 3923893
  have htrace : WordTrace (prefixWord ++ tailWord_3923893) baseStart_3923893 baseEnd_3923893 := by
    simpa [prefixWord, tailWord_3923893, baseEnd_3923893] using wordTrace_append hprefix tailTrace_3923893
  have hstable : (prefixWord ++ tailWord_3923893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923893).length < 2 ^ (prefixWord ++ tailWord_3923893).sum := by decide
  have hdescent : baseEnd_3923893 < baseStart_3923893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923951 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 2, 6]
def baseStart_3923951 : Nat := 118140960795 + 3923951 * 2 ^ 59
def prefixEnd_3923951 : Nat := 4983230072969 + 3 ^ 40 * 3923951 * 2
def baseEnd_3923951 : Nat := 1343248618460454838244389

theorem tailTrace_3923951 : CollatzResearch.WordTrace tailWord_3923951 prefixEnd_3923951 1343248618460454838244389 := by
  unfold tailWord_3923951
  simp only [CollatzResearch.WordTrace]
  refine ⟨143118250607203159321947707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95412167071468772881298471 143118250607203159321947707)
  ·
    refine ⟨214677375910804738982921561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143118250607203159321947707 214677375910804738982921561)
    ·
      refine ⟨161008031933103554237191171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214677375910804738982921561 161008031933103554237191171)
      ·
        refine ⟨241512047899655331355786757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161008031933103554237191171 241512047899655331355786757)
        ·
          refine ⟨45283508981185374629210017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241512047899655331355786757 45283508981185374629210017)
          ·
            refine ⟨33962631735889030971907513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45283508981185374629210017 33962631735889030971907513)
            ·
              refine ⟨25471973801916773228930635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33962631735889030971907513 25471973801916773228930635)
              ·
                refine ⟨38207960702875159843395953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25471973801916773228930635 38207960702875159843395953)
                ·
                  refine ⟨28655970527156369882546965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38207960702875159843395953 28655970527156369882546965)
                  ·
                    refine ⟨1343248618460454838244389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28655970527156369882546965 1343248618460454838244389)
                    ·
                      rfl

theorem cell22_3923951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_3923951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923951 prefixEnd_3923951 := by exact prefixLift 3923951
  have htrace : WordTrace (prefixWord ++ tailWord_3923951) baseStart_3923951 baseEnd_3923951 := by
    simpa [prefixWord, tailWord_3923951, baseEnd_3923951] using wordTrace_append hprefix tailTrace_3923951
  have hstable : (prefixWord ++ tailWord_3923951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923951).length < 2 ^ (prefixWord ++ tailWord_3923951).sum := by decide
  have hdescent : baseEnd_3923951 < baseStart_3923951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924004 : List Nat := [2, 3, 1, 4, 2, 1, 1, 4, 1, 3]
def baseStart_3924004 : Nat := 118140960795 + 3924004 * 2 ^ 59
def prefixEnd_3924004 : Nat := 4983230072969 + 3 ^ 40 * 3924004 * 2
def baseEnd_3924004 : Nat := 1343266761443580366669227

theorem tailTrace_3924004 : CollatzResearch.WordTrace tailWord_3924004 prefixEnd_3924004 1343266761443580366669227 := by
  unfold tailWord_3924004
  simp only [CollatzResearch.WordTrace]
  refine ⟨71560091838005574686813533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95413455784007432915751377 71560091838005574686813533)
  ·
    refine ⟨26835034439252090507555075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71560091838005574686813533 26835034439252090507555075)
    ·
      refine ⟨40252551658878135761332613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26835034439252090507555075 40252551658878135761332613)
      ·
        refine ⟨7547353436039650455249865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40252551658878135761332613 7547353436039650455249865)
        ·
          refine ⟨5660515077029737841437399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7547353436039650455249865 5660515077029737841437399)
          ·
            refine ⟨8490772615544606762156099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5660515077029737841437399 8490772615544606762156099)
            ·
              refine ⟨12736158923316910143234149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8490772615544606762156099 12736158923316910143234149)
              ·
                refine ⟨2388029798121920651856403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12736158923316910143234149 2388029798121920651856403)
                ·
                  refine ⟨3582044697182880977784605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2388029798121920651856403 3582044697182880977784605)
                  ·
                    refine ⟨1343266761443580366669227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3582044697182880977784605 1343266761443580366669227)
                    ·
                      rfl

theorem cell22_3924004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_3924004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924004 prefixEnd_3924004 := by exact prefixLift 3924004
  have htrace : WordTrace (prefixWord ++ tailWord_3924004) baseStart_3924004 baseEnd_3924004 := by
    simpa [prefixWord, tailWord_3924004, baseEnd_3924004] using wordTrace_append hprefix tailTrace_3924004
  have hstable : (prefixWord ++ tailWord_3924004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924004).length < 2 ^ (prefixWord ++ tailWord_3924004).sum := by decide
  have hdescent : baseEnd_3924004 < baseStart_3924004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924028 : List Nat := [2, 2, 2, 2, 2, 1, 3, 2, 6]
def baseStart_3924028 : Nat := 118140960795 + 3924028 * 2 ^ 59
def prefixEnd_3924028 : Nat := 4983230072969 + 3 ^ 40 * 3924028 * 2
def baseEnd_3924028 : Nat := 447758325711350768023051

theorem tailTrace_3924028 : CollatzResearch.WordTrace tailWord_3924028 prefixEnd_3924028 447758325711350768023051 := by
  unfold tailWord_3924028
  simp only [CollatzResearch.WordTrace]
  refine ⟨71560529513962100736250369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95414039351949467648333825 71560529513962100736250369)
  ·
    refine ⟨53670397135471575552187777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71560529513962100736250369 53670397135471575552187777)
    ·
      refine ⟨40252797851603681664140833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53670397135471575552187777 40252797851603681664140833)
      ·
        refine ⟨30189598388702761248105625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40252797851603681664140833 30189598388702761248105625)
        ·
          refine ⟨22642198791527070936079219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30189598388702761248105625 22642198791527070936079219)
          ·
            refine ⟨33963298187290606404118829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22642198791527070936079219 33963298187290606404118829)
            ·
              refine ⟨12736236820233977401544561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33963298187290606404118829 12736236820233977401544561)
              ·
                refine ⟨9552177615175483051158421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12736236820233977401544561 9552177615175483051158421)
                ·
                  refine ⟨447758325711350768023051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9552177615175483051158421 447758325711350768023051)
                  ·
                    rfl

theorem cell22_3924028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_3924028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924028 prefixEnd_3924028 := by exact prefixLift 3924028
  have htrace : WordTrace (prefixWord ++ tailWord_3924028) baseStart_3924028 baseEnd_3924028 := by
    simpa [prefixWord, tailWord_3924028, baseEnd_3924028] using wordTrace_append hprefix tailTrace_3924028
  have hstable : (prefixWord ++ tailWord_3924028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924028).length < 2 ^ (prefixWord ++ tailWord_3924028).sum := by decide
  have hdescent : baseEnd_3924028 < baseStart_3924028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924043 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 6, 3]
def baseStart_3924043 : Nat := 118140960795 + 3924043 * 2 ^ 59
def prefixEnd_3924043 : Nat := 4983230072969 + 3 ^ 40 * 3924043 * 2
def baseEnd_3924043 : Nat := 1343280111940597264944107

theorem tailTrace_3924043 : CollatzResearch.WordTrace tailWord_3924043 prefixEnd_3924043 1343280111940597264944107 := by
  unfold tailWord_3924043
  simp only [CollatzResearch.WordTrace]
  refine ⟨143121606122869859034296783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95414404081913239356197855 143121606122869859034296783)
  ·
    refine ⟨214682409184304788551445175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143121606122869859034296783 214682409184304788551445175)
    ·
      refine ⟨322023613776457182827167763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214682409184304788551445175 322023613776457182827167763)
      ·
        refine ⟨483035420664685774240751645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322023613776457182827167763 483035420664685774240751645)
        ·
          refine ⟨181138282749257165340281867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 483035420664685774240751645 181138282749257165340281867)
          ·
            refine ⟨271707424123885748010422801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181138282749257165340281867 271707424123885748010422801)
            ·
              refine ⟨203780568092914311007817101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271707424123885748010422801 203780568092914311007817101)
              ·
                refine ⟨76417713034842866627931413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203780568092914311007817101 76417713034842866627931413)
                ·
                  refine ⟨3582080298508259373184285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76417713034842866627931413 3582080298508259373184285)
                  ·
                    refine ⟨1343280111940597264944107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3582080298508259373184285 1343280111940597264944107)
                    ·
                      rfl

theorem cell22_3924043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 3].length) (baseStart_3924043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924043 prefixEnd_3924043 := by exact prefixLift 3924043
  have htrace : WordTrace (prefixWord ++ tailWord_3924043) baseStart_3924043 baseEnd_3924043 := by
    simpa [prefixWord, tailWord_3924043, baseEnd_3924043] using wordTrace_append hprefix tailTrace_3924043
  have hstable : (prefixWord ++ tailWord_3924043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924043).length < 2 ^ (prefixWord ++ tailWord_3924043).sum := by decide
  have hdescent : baseEnd_3924043 < baseStart_3924043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924058 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 4, 4]
def baseStart_3924058 : Nat := 118140960795 + 3924058 * 2 ^ 59
def prefixEnd_3924058 : Nat := 4983230072969 + 3 ^ 40 * 3924058 * 2
def baseEnd_3924058 : Nat := 1343285246747142225819061

theorem tailTrace_3924058 : CollatzResearch.WordTrace tailWord_3924058 prefixEnd_3924058 1343285246747142225819061 := by
  unfold tailWord_3924058
  simp only [CollatzResearch.WordTrace]
  refine ⟨35780538304453879149023207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95414768811877011064061885 35780538304453879149023207)
  ·
    refine ⟨53670807456680818723534811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35780538304453879149023207 53670807456680818723534811)
    ·
      refine ⟨80506211185021228085302217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53670807456680818723534811 80506211185021228085302217)
      ·
        refine ⟨60379658388765921063976663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80506211185021228085302217 60379658388765921063976663)
        ·
          refine ⟨90569487583148881595964995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60379658388765921063976663 90569487583148881595964995)
          ·
            refine ⟨135854231374723322393947493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90569487583148881595964995 135854231374723322393947493)
            ·
              refine ⟨25472668382760622948865155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135854231374723322393947493 25472668382760622948865155)
              ·
                refine ⟨38209002574140934423297733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25472668382760622948865155 38209002574140934423297733)
                ·
                  refine ⟨7164187982651425204368325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38209002574140934423297733 7164187982651425204368325)
                  ·
                    refine ⟨1343285246747142225819061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7164187982651425204368325 1343285246747142225819061)
                    ·
                      rfl

theorem cell22_3924058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_3924058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924058 prefixEnd_3924058 := by exact prefixLift 3924058
  have htrace : WordTrace (prefixWord ++ tailWord_3924058) baseStart_3924058 baseEnd_3924058 := by
    simpa [prefixWord, tailWord_3924058, baseEnd_3924058] using wordTrace_append hprefix tailTrace_3924058
  have hstable : (prefixWord ++ tailWord_3924058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924058).length < 2 ^ (prefixWord ++ tailWord_3924058).sum := by decide
  have hdescent : baseEnd_3924058 < baseStart_3924058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924133 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 1, 7]
def baseStart_3924133 : Nat := 118140960795 + 3924133 * 2 ^ 59
def prefixEnd_3924133 : Nat := 4983230072969 + 3 ^ 40 * 3924133 * 2
def baseEnd_3924133 : Nat := 1343310920779867030193831

theorem tailTrace_3924133 : CollatzResearch.WordTrace tailWord_3924133 prefixEnd_3924133 1343310920779867030193831 := by
  unfold tailWord_3924133
  simp only [CollatzResearch.WordTrace]
  refine ⟨143124888692543804405073053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95416592461695869603382035 143124888692543804405073053)
  ·
    refine ⟨53671833259703926651902395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143124888692543804405073053 53671833259703926651902395)
    ·
      refine ⟨80507749889555889977853593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53671833259703926651902395 80507749889555889977853593)
      ·
        refine ⟨60380812417166917483390195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80507749889555889977853593 60380812417166917483390195)
        ·
          refine ⟨90571218625750376225085293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60380812417166917483390195 90571218625750376225085293)
          ·
            refine ⟨33964206984656391084406985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90571218625750376225085293 33964206984656391084406985)
            ·
              refine ⟨25473155238492293313305239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33964206984656391084406985 25473155238492293313305239)
              ·
                refine ⟨38209732857738439969957859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25473155238492293313305239 38209732857738439969957859)
                ·
                  refine ⟨57314599286607659954936789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38209732857738439969957859 57314599286607659954936789)
                  ·
                    refine ⟨1343310920779867030193831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57314599286607659954936789 1343310920779867030193831)
                    ·
                      rfl

theorem cell22_3924133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_3924133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924133 prefixEnd_3924133 := by exact prefixLift 3924133
  have htrace : WordTrace (prefixWord ++ tailWord_3924133) baseStart_3924133 baseEnd_3924133 := by
    simpa [prefixWord, tailWord_3924133, baseEnd_3924133] using wordTrace_append hprefix tailTrace_3924133
  have hstable : (prefixWord ++ tailWord_3924133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924133).length < 2 ^ (prefixWord ++ tailWord_3924133).sum := by decide
  have hdescent : baseEnd_3924133 < baseStart_3924133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924165 : List Nat := [1, 3, 1, 1, 1, 1, 4, 5, 1, 4]
def baseStart_3924165 : Nat := 118140960795 + 3924165 * 2 ^ 59
def prefixEnd_3924165 : Nat := 4983230072969 + 3 ^ 40 * 3924165 * 2
def baseEnd_3924165 : Nat := 1343321875033829613393733

theorem tailTrace_3924165 : CollatzResearch.WordTrace tailWord_3924165 prefixEnd_3924165 1343321875033829613393733 := by
  unfold tailWord_3924165
  simp only [CollatzResearch.WordTrace]
  refine ⟨143126055828427873870237949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95417370552285249246825299 143126055828427873870237949)
  ·
    refine ⟨53672270935660452701339231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143126055828427873870237949 53672270935660452701339231)
    ·
      refine ⟨80508406403490679052008847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53672270935660452701339231 80508406403490679052008847)
      ·
        refine ⟨120762609605236018578013271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80508406403490679052008847 120762609605236018578013271)
        ·
          refine ⟨181143914407854027867019907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120762609605236018578013271 181143914407854027867019907)
          ·
            refine ⟨271715871611781041800529861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181143914407854027867019907 271715871611781041800529861)
            ·
              refine ⟨50946725927208945337599349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 271715871611781041800529861 50946725927208945337599349)
              ·
                refine ⟨4776255555675838625399939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50946725927208945337599349 4776255555675838625399939)
                ·
                  refine ⟨7164383333513757938099909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776255555675838625399939 7164383333513757938099909)
                  ·
                    refine ⟨1343321875033829613393733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7164383333513757938099909 1343321875033829613393733)
                    ·
                      rfl

theorem cell22_3924165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_3924165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924165 prefixEnd_3924165 := by exact prefixLift 3924165
  have htrace : WordTrace (prefixWord ++ tailWord_3924165) baseStart_3924165 baseEnd_3924165 := by
    simpa [prefixWord, tailWord_3924165, baseEnd_3924165] using wordTrace_append hprefix tailTrace_3924165
  have hstable : (prefixWord ++ tailWord_3924165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924165).length < 2 ^ (prefixWord ++ tailWord_3924165).sum := by decide
  have hdescent : baseEnd_3924165 < baseStart_3924165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924208 : List Nat := [2, 1, 1, 1, 3, 1, 1, 12]
def baseStart_3924208 : Nat := 118140960795 + 3924208 * 2 ^ 59
def prefixEnd_3924208 : Nat := 4983230072969 + 3 ^ 40 * 3924208 * 2
def baseEnd_3924208 : Nat := 149259621645843537174289

theorem tailTrace_3924208 : CollatzResearch.WordTrace tailWord_3924208 prefixEnd_3924208 149259621645843537174289 := by
  unfold tailWord_3924208
  simp only [CollatzResearch.WordTrace]
  refine ⟨71563812083636046107026639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95418416111514728142702185 71563812083636046107026639)
  ·
    refine ⟨107345718125454069160539959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71563812083636046107026639 107345718125454069160539959)
    ·
      refine ⟨161018577188181103740809939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107345718125454069160539959 161018577188181103740809939)
      ·
        refine ⟨241527865782271655611214909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161018577188181103740809939 241527865782271655611214909)
        ·
          refine ⟨90572949668351870854205591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241527865782271655611214909 90572949668351870854205591)
          ·
            refine ⟨135859424502527806281308387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90572949668351870854205591 135859424502527806281308387)
            ·
              refine ⟨203789136753791709421962581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135859424502527806281308387 203789136753791709421962581)
              ·
                refine ⟨149259621645843537174289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 203789136753791709421962581 149259621645843537174289)
                ·
                  rfl

theorem cell22_3924208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 12].length) (baseStart_3924208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924208 prefixEnd_3924208 := by exact prefixLift 3924208
  have htrace : WordTrace (prefixWord ++ tailWord_3924208) baseStart_3924208 baseEnd_3924208 := by
    simpa [prefixWord, tailWord_3924208, baseEnd_3924208] using wordTrace_append hprefix tailTrace_3924208
  have hstable : (prefixWord ++ tailWord_3924208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924208).length < 2 ^ (prefixWord ++ tailWord_3924208).sum := by decide
  have hdescent : baseEnd_3924208 < baseStart_3924208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924257 : List Nat := [1, 2, 3, 2, 1, 1, 4, 2, 3, 3]
def baseStart_3924257 : Nat := 118140960795 + 3924257 * 2 ^ 59
def prefixEnd_3924257 : Nat := 4983230072969 + 3 ^ 40 * 3924257 * 2
def baseEnd_3924257 : Nat := 1343353368513972040093451

theorem tailTrace_3924257 : CollatzResearch.WordTrace tailWord_3924257 prefixEnd_3924257 1343353368513972040093451 := by
  unfold tailWord_3924257
  simp only [CollatzResearch.WordTrace]
  refine ⟨143129411344094573582587025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95419607562729715721724683 143129411344094573582587025)
  ·
    refine ⟨107347058508070930186940269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143129411344094573582587025 107347058508070930186940269)
    ·
      refine ⟨40255146940526598820102601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107347058508070930186940269 40255146940526598820102601)
      ·
        refine ⟨30191360205394949115076951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40255146940526598820102601 30191360205394949115076951)
        ·
          refine ⟨45287040308092423672615427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30191360205394949115076951 45287040308092423672615427)
          ·
            refine ⟨67930560462138635508923141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45287040308092423672615427 67930560462138635508923141)
            ·
              refine ⟨12736980086650994157923089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67930560462138635508923141 12736980086650994157923089)
              ·
                refine ⟨9552735064988245618442317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12736980086650994157923089 9552735064988245618442317)
                ·
                  refine ⟨3582275649370592106915869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9552735064988245618442317 3582275649370592106915869)
                  ·
                    refine ⟨1343353368513972040093451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3582275649370592106915869 1343353368513972040093451)
                    ·
                      rfl

theorem cell22_3924257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_3924257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924257 prefixEnd_3924257 := by exact prefixLift 3924257
  have htrace : WordTrace (prefixWord ++ tailWord_3924257) baseStart_3924257 baseEnd_3924257 := by
    simpa [prefixWord, tailWord_3924257, baseEnd_3924257] using wordTrace_append hprefix tailTrace_3924257
  have hstable : (prefixWord ++ tailWord_3924257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924257).length < 2 ^ (prefixWord ++ tailWord_3924257).sum := by decide
  have hdescent : baseEnd_3924257 < baseStart_3924257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924304 : List Nat := [2, 1, 1, 1, 1, 8, 2, 1, 5]
def baseStart_3924304 : Nat := 118140960795 + 3924304 * 2 ^ 59
def prefixEnd_3924304 : Nat := 4983230072969 + 3 ^ 40 * 3924304 * 2
def baseEnd_3924304 : Nat := 447789819191493194722769

theorem tailTrace_3924304 : CollatzResearch.WordTrace tailWord_3924304 prefixEnd_3924304 447789819191493194722769 := by
  unfold tailWord_3924304
  simp only [CollatzResearch.WordTrace]
  refine ⟨71565562787462150304773983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95420750383282867073031977 71565562787462150304773983)
  ·
    refine ⟨107348344181193225457160975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71565562787462150304773983 107348344181193225457160975)
    ·
      refine ⟨161022516271789838185741463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107348344181193225457160975 161022516271789838185741463)
      ·
        refine ⟨241533774407684757278612195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161022516271789838185741463 241533774407684757278612195)
        ·
          refine ⟨362300661611527135917918293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241533774407684757278612195 362300661611527135917918293)
          ·
            refine ⟨4245710878260083624038105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 362300661611527135917918293 4245710878260083624038105)
            ·
              refine ⟨3184283158695062718028579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4245710878260083624038105 3184283158695062718028579)
              ·
                refine ⟨4776424738042594077042869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3184283158695062718028579 4776424738042594077042869)
                ·
                  refine ⟨447789819191493194722769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4776424738042594077042869 447789819191493194722769)
                  ·
                    rfl

theorem cell22_3924304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 5].length) (baseStart_3924304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924304 prefixEnd_3924304 := by exact prefixLift 3924304
  have htrace : WordTrace (prefixWord ++ tailWord_3924304) baseStart_3924304 baseEnd_3924304 := by
    simpa [prefixWord, tailWord_3924304, baseEnd_3924304] using wordTrace_append hprefix tailTrace_3924304
  have hstable : (prefixWord ++ tailWord_3924304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924304).length < 2 ^ (prefixWord ++ tailWord_3924304).sum := by decide
  have hdescent : baseEnd_3924304 < baseStart_3924304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924342 : List Nat := [5, 1, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_3924342 : Nat := 118140960795 + 3924342 * 2 ^ 59
def prefixEnd_3924342 : Nat := 4983230072969 + 3 ^ 40 * 3924342 * 2
def baseEnd_3924342 : Nat := 1343382465751060151718191

theorem tailTrace_3924342 : CollatzResearch.WordTrace tailWord_3924342 prefixEnd_3924342 1343382465751060151718191 := by
  unfold tailWord_3924342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8945781971799164568714455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95421674365857755399620853 8945781971799164568714455)
  ·
    refine ⟨13418672957698746853071683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8945781971799164568714455 13418672957698746853071683)
    ·
      refine ⟨20128009436548120279607525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13418672957698746853071683 20128009436548120279607525)
      ·
        refine ⟨3774001769352772552426411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20128009436548120279607525 3774001769352772552426411)
        ·
          refine ⟨5661002654029158828639617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3774001769352772552426411 5661002654029158828639617)
          ·
            refine ⟨4245751990521869121479713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5661002654029158828639617 4245751990521869121479713)
            ·
              refine ⟨3184313992891401841109785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4245751990521869121479713 3184313992891401841109785)
              ·
                refine ⟨2388235494668551380832339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3184313992891401841109785 2388235494668551380832339)
                ·
                  refine ⟨3582353242002827071248509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2388235494668551380832339 3582353242002827071248509)
                  ·
                    refine ⟨1343382465751060151718191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3582353242002827071248509 1343382465751060151718191)
                    ·
                      rfl

theorem cell22_3924342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_3924342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924342 prefixEnd_3924342 := by exact prefixLift 3924342
  have htrace : WordTrace (prefixWord ++ tailWord_3924342) baseStart_3924342 baseEnd_3924342 := by
    simpa [prefixWord, tailWord_3924342, baseEnd_3924342] using wordTrace_append hprefix tailTrace_3924342
  have hstable : (prefixWord ++ tailWord_3924342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924342).length < 2 ^ (prefixWord ++ tailWord_3924342).sum := by decide
  have hdescent : baseEnd_3924342 < baseStart_3924342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924345 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 3, 6]
def baseStart_3924345 : Nat := 118140960795 + 3924345 * 2 ^ 59
def prefixEnd_3924345 : Nat := 4983230072969 + 3 ^ 40 * 3924345 * 2
def baseEnd_3924345 : Nat := 1343383492712369143893181

theorem tailTrace_3924345 : CollatzResearch.WordTrace tailWord_3924345 prefixEnd_3924345 1343383492712369143893181 := by
  unfold tailWord_3924345
  simp only [CollatzResearch.WordTrace]
  refine ⟨143132620967775764611790489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95421747311850509741193659 143132620967775764611790489)
  ·
    refine ⟨107349465725831823458842867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143132620967775764611790489 107349465725831823458842867)
    ·
      refine ⟨161024198588747735188264301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107349465725831823458842867 161024198588747735188264301)
      ·
        refine ⟨60384074470780400695599113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161024198588747735188264301 60384074470780400695599113)
        ·
          refine ⟨45288055853085300521699335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60384074470780400695599113 45288055853085300521699335)
          ·
            refine ⟨67932083779627950782549003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45288055853085300521699335 67932083779627950782549003)
            ·
              refine ⟨101898125669441926173823505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67932083779627950782549003 101898125669441926173823505)
              ·
                refine ⟨76423594252081444630367629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101898125669441926173823505 76423594252081444630367629)
                ·
                  refine ⟨28658847844530541736387861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76423594252081444630367629 28658847844530541736387861)
                  ·
                    refine ⟨1343383492712369143893181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28658847844530541736387861 1343383492712369143893181)
                    ·
                      rfl

theorem cell22_3924345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_3924345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924345 prefixEnd_3924345 := by exact prefixLift 3924345
  have htrace : WordTrace (prefixWord ++ tailWord_3924345) baseStart_3924345 baseEnd_3924345 := by
    simpa [prefixWord, tailWord_3924345, baseEnd_3924345] using wordTrace_append hprefix tailTrace_3924345
  have hstable : (prefixWord ++ tailWord_3924345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924345).length < 2 ^ (prefixWord ++ tailWord_3924345).sum := by decide
  have hdescent : baseEnd_3924345 < baseStart_3924345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924349 : List Nat := [1, 4, 1, 1, 2, 4, 1, 4, 4]
def baseStart_3924349 : Nat := 118140960795 + 3924349 * 2 ^ 59
def prefixEnd_3924349 : Nat := 4983230072969 + 3 ^ 40 * 3924349 * 2
def baseEnd_3924349 : Nat := 447794953998038155597723

theorem tailTrace_3924349 : CollatzResearch.WordTrace tailWord_3924349 prefixEnd_3924349 447794953998038155597723 := by
  unfold tailWord_3924349
  simp only [CollatzResearch.WordTrace]
  refine ⟨143132766859761273294936101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95421844573174182196624067 143132766859761273294936101)
  ·
    refine ⟨26837393786205238742800519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143132766859761273294936101 26837393786205238742800519)
    ·
      refine ⟨40256090679307858114200779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26837393786205238742800519 40256090679307858114200779)
      ·
        refine ⟨60384136018961787171301169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40256090679307858114200779 60384136018961787171301169)
        ·
          refine ⟨45288102014221340378475877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60384136018961787171301169 45288102014221340378475877)
          ·
            refine ⟨8491519127666501320964227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45288102014221340378475877 8491519127666501320964227)
            ·
              refine ⟨12737278691499751981446341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8491519127666501320964227 12737278691499751981446341)
              ·
                refine ⟨2388239754656203496521189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12737278691499751981446341 2388239754656203496521189)
                ·
                  refine ⟨447794953998038155597723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2388239754656203496521189 447794953998038155597723)
                  ·
                    rfl

theorem cell22_3924349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_3924349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924349 prefixEnd_3924349 := by exact prefixLift 3924349
  have htrace : WordTrace (prefixWord ++ tailWord_3924349) baseStart_3924349 baseEnd_3924349 := by
    simpa [prefixWord, tailWord_3924349, baseEnd_3924349] using wordTrace_append hprefix tailTrace_3924349
  have hstable : (prefixWord ++ tailWord_3924349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924349).length < 2 ^ (prefixWord ++ tailWord_3924349).sum := by decide
  have hdescent : baseEnd_3924349 < baseStart_3924349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924364 : List Nat := [2, 2, 1, 2, 1, 4, 2, 3, 2, 3]
def baseStart_3924364 : Nat := 118140960795 + 3924364 * 2 ^ 59
def prefixEnd_3924364 : Nat := 4983230072969 + 3 ^ 40 * 3924364 * 2
def baseEnd_3924364 : Nat := 1343389996800659427668123

theorem tailTrace_3924364 : CollatzResearch.WordTrace tailWord_3924364 prefixEnd_3924364 1343389996800659427668123 := by
  unfold tailWord_3924364
  simp only [CollatzResearch.WordTrace]
  refine ⟨71566656977353465428366073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95422209303137953904488097 71566656977353465428366073)
  ·
    refine ⟨53674992733015099071274555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71566656977353465428366073 53674992733015099071274555)
    ·
      refine ⟨80512489099522648606911833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53674992733015099071274555 80512489099522648606911833)
      ·
        refine ⟨60384366824641986455183875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80512489099522648606911833 60384366824641986455183875)
        ·
          refine ⟨90576550236962979682775813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60384366824641986455183875 90576550236962979682775813)
          ·
            refine ⟨16983103169430558690520465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90576550236962979682775813 16983103169430558690520465)
            ·
              refine ⟨12737327377072919017890349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16983103169430558690520465 12737327377072919017890349)
              ·
                refine ⟨4776497766402344631708881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12737327377072919017890349 4776497766402344631708881)
                ·
                  refine ⟨3582373324801758473781661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4776497766402344631708881 3582373324801758473781661)
                  ·
                    refine ⟨1343389996800659427668123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3582373324801758473781661 1343389996800659427668123)
                    ·
                      rfl

theorem cell22_3924364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_3924364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924364 prefixEnd_3924364 := by exact prefixLift 3924364
  have htrace : WordTrace (prefixWord ++ tailWord_3924364) baseStart_3924364 baseEnd_3924364 := by
    simpa [prefixWord, tailWord_3924364, baseEnd_3924364] using wordTrace_append hprefix tailTrace_3924364
  have hstable : (prefixWord ++ tailWord_3924364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924364).length < 2 ^ (prefixWord ++ tailWord_3924364).sum := by decide
  have hdescent : baseEnd_3924364 < baseStart_3924364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924377 : List Nat := [1, 2, 1, 2, 1, 4, 5, 6]
def baseStart_3924377 : Nat := 118140960795 + 3924377 * 2 ^ 59
def prefixEnd_3924377 : Nat := 4983230072969 + 3 ^ 40 * 3924377 * 2
def baseEnd_3924377 : Nat := 149266049662925747454787

theorem tailTrace_3924377 : CollatzResearch.WordTrace tailWord_3924377 prefixEnd_3924377 149266049662925747454787 := by
  unfold tailWord_3924377
  simp only [CollatzResearch.WordTrace]
  refine ⟨143133788103659834076955385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95422525402439889384636923 143133788103659834076955385)
  ·
    refine ⟨107350341077744875557716539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143133788103659834076955385 107350341077744875557716539)
    ·
      refine ⟨161025511616617313336574809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107350341077744875557716539 161025511616617313336574809)
      ·
        refine ⟨120769133712462985002431107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161025511616617313336574809 120769133712462985002431107)
        ·
          refine ⟨181153700568694477503646661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120769133712462985002431107 181153700568694477503646661)
          ·
            refine ⟨33966318856630214531933749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181153700568694477503646661 33966318856630214531933749)
            ·
              refine ⟨3184342392809082612368789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33966318856630214531933749 3184342392809082612368789)
              ·
                refine ⟨149266049662925747454787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3184342392809082612368789 149266049662925747454787)
                ·
                  rfl

theorem cell22_3924377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 6].length) (baseStart_3924377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924377 prefixEnd_3924377 := by exact prefixLift 3924377
  have htrace : WordTrace (prefixWord ++ tailWord_3924377) baseStart_3924377 baseEnd_3924377 := by
    simpa [prefixWord, tailWord_3924377, baseEnd_3924377] using wordTrace_append hprefix tailTrace_3924377
  have hstable : (prefixWord ++ tailWord_3924377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924377).length < 2 ^ (prefixWord ++ tailWord_3924377).sum := by decide
  have hdescent : baseEnd_3924377 < baseStart_3924377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924385 : List Nat := [1, 2, 3, 5, 2, 1, 2, 1, 1, 4]
def baseStart_3924385 : Nat := 118140960795 + 3924385 * 2 ^ 59
def prefixEnd_3924385 : Nat := 4983230072969 + 3 ^ 40 * 3924385 * 2
def baseEnd_3924385 : Nat := 1343397185529822372893059

theorem tailTrace_3924385 : CollatzResearch.WordTrace tailWord_3924385 prefixEnd_3924385 1343397185529822372893059 := by
  unfold tailWord_3924385
  simp only [CollatzResearch.WordTrace]
  refine ⟨143134079887630851443246609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95422719925087234295497739 143134079887630851443246609)
  ·
    refine ⟨107350559915723138582434957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143134079887630851443246609 107350559915723138582434957)
    ·
      refine ⟨40256459968396176968413109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107350559915723138582434957 40256459968396176968413109)
      ·
        refine ⟨3774043122037141590788729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40256459968396176968413109 3774043122037141590788729)
        ·
          refine ⟨2830532341527856193091547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3774043122037141590788729 2830532341527856193091547)
          ·
            refine ⟨4245798512291784289637321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830532341527856193091547 4245798512291784289637321)
            ·
              refine ⟨3184348884218838217227991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4245798512291784289637321 3184348884218838217227991)
              ·
                refine ⟨4776523326328257325841987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3184348884218838217227991 4776523326328257325841987)
                ·
                  refine ⟨7164784989492385988762981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776523326328257325841987 7164784989492385988762981)
                  ·
                    refine ⟨1343397185529822372893059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7164784989492385988762981 1343397185529822372893059)
                    ·
                      rfl

theorem cell22_3924385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_3924385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924385 prefixEnd_3924385 := by exact prefixLift 3924385
  have htrace : WordTrace (prefixWord ++ tailWord_3924385) baseStart_3924385 baseEnd_3924385 := by
    simpa [prefixWord, tailWord_3924385, baseEnd_3924385] using wordTrace_append hprefix tailTrace_3924385
  have hstable : (prefixWord ++ tailWord_3924385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924385).length < 2 ^ (prefixWord ++ tailWord_3924385).sum := by decide
  have hdescent : baseEnd_3924385 < baseStart_3924385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924409 : List Nat := [1, 2, 1, 4, 3, 1, 1, 3, 3, 3]
def baseStart_3924409 : Nat := 118140960795 + 3924409 * 2 ^ 59
def prefixEnd_3924409 : Nat := 4983230072969 + 3 ^ 40 * 3924409 * 2
def baseEnd_3924409 : Nat := 1343405401220294310292985

theorem tailTrace_3924409 : CollatzResearch.WordTrace tailWord_3924409 prefixEnd_3924409 1343405401220294310292985 := by
  unfold tailWord_3924409
  simp only [CollatzResearch.WordTrace]
  refine ⟨143134955239543903542120281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95423303493029269028080187 143134955239543903542120281)
  ·
    refine ⟨107351216429657927656590211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143134955239543903542120281 107351216429657927656590211)
    ·
      refine ⟨161026824644486891484885317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107351216429657927656590211 161026824644486891484885317)
      ·
        refine ⟨30192529620841292153415997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161026824644486891484885317 30192529620841292153415997)
        ·
          refine ⟨11322198607815484557530999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30192529620841292153415997 11322198607815484557530999)
          ·
            refine ⟨16983297911723226836296499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11322198607815484557530999 16983297911723226836296499)
            ·
              refine ⟨25474946867584840254444749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16983297911723226836296499 25474946867584840254444749)
              ·
                refine ⟨9553105075344315095416781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25474946867584840254444749 9553105075344315095416781)
                ·
                  refine ⟨3582414403254118160781293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9553105075344315095416781 3582414403254118160781293)
                  ·
                    refine ⟨1343405401220294310292985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3582414403254118160781293 1343405401220294310292985)
                    ·
                      rfl

theorem cell22_3924409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 3].length) (baseStart_3924409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924409 prefixEnd_3924409 := by exact prefixLift 3924409
  have htrace : WordTrace (prefixWord ++ tailWord_3924409) baseStart_3924409 baseEnd_3924409 := by
    simpa [prefixWord, tailWord_3924409, baseEnd_3924409] using wordTrace_append hprefix tailTrace_3924409
  have hstable : (prefixWord ++ tailWord_3924409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924409).length < 2 ^ (prefixWord ++ tailWord_3924409).sum := by decide
  have hdescent : baseEnd_3924409 < baseStart_3924409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924452 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_3924452 : Nat := 118140960795 + 3924452 * 2 ^ 59
def prefixEnd_3924452 : Nat := 4983230072969 + 3 ^ 40 * 3924452 * 2
def baseEnd_3924452 : Nat := 1343420120999056531467853

theorem tailTrace_3924452 : CollatzResearch.WordTrace tailWord_3924452 prefixEnd_3924452 1343420120999056531467853 := by
  unfold tailWord_3924452
  simp only [CollatzResearch.WordTrace]
  refine ⟨71568261789194060942967805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95424349052258747923957073 71568261789194060942967805)
  ·
    refine ⟨26838098170947772853612927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71568261789194060942967805 26838098170947772853612927)
    ·
      refine ⟨40257147256421659280419391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26838098170947772853612927 40257147256421659280419391)
      ·
        refine ⟨60385720884632488920629087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40257147256421659280419391 60385720884632488920629087)
        ·
          refine ⟨90578581326948733380943631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60385720884632488920629087 90578581326948733380943631)
          ·
            refine ⟨135867871990423100071415447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90578581326948733380943631 135867871990423100071415447)
            ·
              refine ⟨203801807985634650107123171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135867871990423100071415447 203801807985634650107123171)
              ·
                refine ⟨305702711978451975160684757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203801807985634650107123171 305702711978451975160684757)
                ·
                  refine ⟨7164907311994968167828549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 305702711978451975160684757 7164907311994968167828549)
                  ·
                    refine ⟨1343420120999056531467853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7164907311994968167828549 1343420120999056531467853)
                    ·
                      rfl

theorem cell22_3924452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_3924452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924452 prefixEnd_3924452 := by exact prefixLift 3924452
  have htrace : WordTrace (prefixWord ++ tailWord_3924452) baseStart_3924452 baseEnd_3924452 := by
    simpa [prefixWord, tailWord_3924452, baseEnd_3924452] using wordTrace_append hprefix tailTrace_3924452
  have hstable : (prefixWord ++ tailWord_3924452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924452).length < 2 ^ (prefixWord ++ tailWord_3924452).sum := by decide
  have hdescent : baseEnd_3924452 < baseStart_3924452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924512 : List Nat := [2, 1, 1, 6, 12]
def baseStart_3924512 : Nat := 118140960795 + 3924512 * 2 ^ 59
def prefixEnd_3924512 : Nat := 4983230072969 + 3 ^ 40 * 3924512 * 2
def baseEnd_3924512 : Nat := 5528562387758174382583

theorem tailTrace_3924512 : CollatzResearch.WordTrace tailWord_3924512 prefixEnd_3924512 5528562387758174382583 := by
  unfold tailWord_3924512
  simp only [CollatzResearch.WordTrace]
  refine ⟨71569355979085376066559895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95425807972113834755413193 71569355979085376066559895)
  ·
    refine ⟨107354033968628064099839843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71569355979085376066559895 107354033968628064099839843)
    ·
      refine ⟨161031050952942096149759765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107354033968628064099839843 161031050952942096149759765)
      ·
        refine ⟨7548330513419160757019989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 161031050952942096149759765 7548330513419160757019989)
        ·
          refine ⟨5528562387758174382583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7548330513419160757019989 5528562387758174382583)
          ·
            rfl

theorem cell22_3924512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 12].length) (baseStart_3924512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924512 prefixEnd_3924512 := by exact prefixLift 3924512
  have htrace : WordTrace (prefixWord ++ tailWord_3924512) baseStart_3924512 baseEnd_3924512 := by
    simpa [prefixWord, tailWord_3924512, baseEnd_3924512] using wordTrace_append hprefix tailTrace_3924512
  have hstable : (prefixWord ++ tailWord_3924512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924512).length < 2 ^ (prefixWord ++ tailWord_3924512).sum := by decide
  have hdescent : baseEnd_3924512 < baseStart_3924512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924544 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 5, 3]
def baseStart_3924544 : Nat := 118140960795 + 3924544 * 2 ^ 59
def prefixEnd_3924544 : Nat := 4983230072969 + 3 ^ 40 * 3924544 * 2
def baseEnd_3924544 : Nat := 1343451614479198958167571

theorem tailTrace_3924544 : CollatzResearch.WordTrace tailWord_3924544 prefixEnd_3924544 1343451614479198958167571 := by
  unfold tailWord_3924544
  simp only [CollatzResearch.WordTrace]
  refine ⟨71569939547027410799142343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95426586062703214398856457 71569939547027410799142343)
  ·
    refine ⟨107354909320541116198713515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71569939547027410799142343 107354909320541116198713515)
    ·
      refine ⟨161032363980811674298070273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107354909320541116198713515 161032363980811674298070273)
      ·
        refine ⟨120774272985608755723552705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161032363980811674298070273 120774272985608755723552705)
        ·
          refine ⟨90580704739206566792664529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120774272985608755723552705 90580704739206566792664529)
          ·
            refine ⟨67935528554404925094498397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90580704739206566792664529 67935528554404925094498397)
            ·
              refine ⟨25475823207901846910436899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67935528554404925094498397 25475823207901846910436899)
              ·
                refine ⟨38213734811852770365655349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25475823207901846910436899 38213734811852770365655349)
                ·
                  refine ⟨3582537638611197221780189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38213734811852770365655349 3582537638611197221780189)
                  ·
                    refine ⟨1343451614479198958167571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3582537638611197221780189 1343451614479198958167571)
                    ·
                      rfl

theorem cell22_3924544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 5, 3].length) (baseStart_3924544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924544 prefixEnd_3924544 := by exact prefixLift 3924544
  have htrace : WordTrace (prefixWord ++ tailWord_3924544) baseStart_3924544 baseEnd_3924544 := by
    simpa [prefixWord, tailWord_3924544, baseEnd_3924544] using wordTrace_append hprefix tailTrace_3924544
  have hstable : (prefixWord ++ tailWord_3924544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924544).length < 2 ^ (prefixWord ++ tailWord_3924544).sum := by decide
  have hdescent : baseEnd_3924544 < baseStart_3924544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924587 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 2, 8]
def baseStart_3924587 : Nat := 118140960795 + 3924587 * 2 ^ 59
def prefixEnd_3924587 : Nat := 4983230072969 + 3 ^ 40 * 3924587 * 2
def baseEnd_3924587 : Nat := 1343466334257961179342439

theorem tailTrace_3924587 : CollatzResearch.WordTrace tailWord_3924587 prefixEnd_3924587 1343466334257961179342439 := by
  unfold tailWord_3924587
  simp only [CollatzResearch.WordTrace]
  refine ⟨143141447432899039942100015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95427631621932693294733343 143141447432899039942100015)
  ·
    refine ⟨214712171149348559913150023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143141447432899039942100015 214712171149348559913150023)
    ·
      refine ⟨322068256724022839869725035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214712171149348559913150023 322068256724022839869725035)
      ·
        refine ⟨483102385086034259804587553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322068256724022839869725035 483102385086034259804587553)
        ·
          refine ⟨362326788814525694853440665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483102385086034259804587553 362326788814525694853440665)
          ·
            refine ⟨271745091610894271140080499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362326788814525694853440665 271745091610894271140080499)
            ·
              refine ⟨407617637416341406710120749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271745091610894271140080499 407617637416341406710120749)
              ·
                refine ⟨152856614031128027516295281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407617637416341406710120749 152856614031128027516295281)
                ·
                  refine ⟨114642460523346020637221461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152856614031128027516295281 114642460523346020637221461)
                  ·
                    refine ⟨1343466334257961179342439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114642460523346020637221461 1343466334257961179342439)
                    ·
                      rfl

theorem cell22_3924587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 8].length) (baseStart_3924587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924587 prefixEnd_3924587 := by exact prefixLift 3924587
  have htrace : WordTrace (prefixWord ++ tailWord_3924587) baseStart_3924587 baseEnd_3924587 := by
    simpa [prefixWord, tailWord_3924587, baseEnd_3924587] using wordTrace_append hprefix tailTrace_3924587
  have hstable : (prefixWord ++ tailWord_3924587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924587).length < 2 ^ (prefixWord ++ tailWord_3924587).sum := by decide
  have hdescent : baseEnd_3924587 < baseStart_3924587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924604 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 3, 4]
def baseStart_3924604 : Nat := 118140960795 + 3924604 * 2 ^ 59
def prefixEnd_3924604 : Nat := 4983230072969 + 3 ^ 40 * 3924604 * 2
def baseEnd_3924604 : Nat := 1343472153705378801667387

theorem tailTrace_3924604 : CollatzResearch.WordTrace tailWord_3924604 prefixEnd_3924604 1343472153705378801667387 := by
  unfold tailWord_3924604
  simp only [CollatzResearch.WordTrace]
  refine ⟨71571033736918725922734433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95428044982558301230312577 71571033736918725922734433)
  ·
    refine ⟨53678275302689044442050825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71571033736918725922734433 53678275302689044442050825)
    ·
      refine ⟨40258706477016783331538119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53678275302689044442050825 40258706477016783331538119)
      ·
        refine ⟨60388059715525174997307179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40258706477016783331538119 60388059715525174997307179)
        ·
          refine ⟨90582089573287762495960769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60388059715525174997307179 90582089573287762495960769)
          ·
            refine ⟨67936567179965821871970577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90582089573287762495960769 67936567179965821871970577)
            ·
              refine ⟨50952425384974366403977933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67936567179965821871970577 50952425384974366403977933)
              ·
                refine ⟨19107159519365387401491725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50952425384974366403977933 19107159519365387401491725)
                ·
                  refine ⟨7165184819762020275559397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19107159519365387401491725 7165184819762020275559397)
                  ·
                    refine ⟨1343472153705378801667387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7165184819762020275559397 1343472153705378801667387)
                    ·
                      rfl

theorem cell22_3924604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_3924604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924604 prefixEnd_3924604 := by exact prefixLift 3924604
  have htrace : WordTrace (prefixWord ++ tailWord_3924604) baseStart_3924604 baseEnd_3924604 := by
    simpa [prefixWord, tailWord_3924604, baseEnd_3924604] using wordTrace_append hprefix tailTrace_3924604
  have hstable : (prefixWord ++ tailWord_3924604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924604).length < 2 ^ (prefixWord ++ tailWord_3924604).sum := by decide
  have hdescent : baseEnd_3924604 < baseStart_3924604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924636 : List Nat := [2, 2, 3, 2, 2, 1, 3, 1, 6]
def baseStart_3924636 : Nat := 118140960795 + 3924636 * 2 ^ 59
def prefixEnd_3924636 : Nat := 4983230072969 + 3 ^ 40 * 3924636 * 2
def baseEnd_3924636 : Nat := 447827702653113794955763

theorem tailTrace_3924636 : CollatzResearch.WordTrace tailWord_3924636 prefixEnd_3924636 447827702653113794955763 := by
  unfold tailWord_3924636
  simp only [CollatzResearch.WordTrace]
  refine ⟨71571617304860760655316881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95428823073147680873755841 71571617304860760655316881)
  ·
    refine ⟨53678712978645570491487661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71571617304860760655316881 53678712978645570491487661)
    ·
      refine ⟨20129517366992088934307873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53678712978645570491487661 20129517366992088934307873)
      ·
        refine ⟨15097138025244066700730905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20129517366992088934307873 15097138025244066700730905)
        ·
          refine ⟨11322853518933050025548179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15097138025244066700730905 11322853518933050025548179)
          ·
            refine ⟨16984280278399575038322269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11322853518933050025548179 16984280278399575038322269)
            ·
              refine ⟨6369105104399840639370851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16984280278399575038322269 6369105104399840639370851)
              ·
                refine ⟨9553657656599760959056277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6369105104399840639370851 9553657656599760959056277)
                ·
                  refine ⟨447827702653113794955763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9553657656599760959056277 447827702653113794955763)
                  ·
                    rfl

theorem cell22_3924636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_3924636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924636 prefixEnd_3924636 := by exact prefixLift 3924636
  have htrace : WordTrace (prefixWord ++ tailWord_3924636) baseStart_3924636 baseEnd_3924636 := by
    simpa [prefixWord, tailWord_3924636, baseEnd_3924636] using wordTrace_append hprefix tailTrace_3924636
  have hstable : (prefixWord ++ tailWord_3924636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924636).length < 2 ^ (prefixWord ++ tailWord_3924636).sum := by decide
  have hdescent : baseEnd_3924636 < baseStart_3924636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924666 : List Nat := [3, 1, 1, 1, 2, 3, 4, 1, 2, 4]
def baseStart_3924666 : Nat := 118140960795 + 3924666 * 2 ^ 59
def prefixEnd_3924666 : Nat := 4983230072969 + 3 ^ 40 * 3924666 * 2
def baseEnd_3924666 : Nat := 1343493377572431306617197

theorem tailTrace_3924666 : CollatzResearch.WordTrace tailWord_3924666 prefixEnd_3924666 1343493377572431306617197 := by
  unfold tailWord_3924666
  simp only [CollatzResearch.WordTrace]
  refine ⟨35786082199903209108556463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95429552533075224289483901 35786082199903209108556463)
  ·
    refine ⟨53679123299854813662834695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35786082199903209108556463 53679123299854813662834695)
    ·
      refine ⟨80518684949782220494252043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53679123299854813662834695 80518684949782220494252043)
      ·
        refine ⟨120778027424673330741378065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80518684949782220494252043 120778027424673330741378065)
        ·
          refine ⟨90583520568504998056033549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120778027424673330741378065 90583520568504998056033549)
          ·
            refine ⟨33968820213189374271012581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90583520568504998056033549 33968820213189374271012581)
            ·
              refine ⟨6369153789973007675814859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33968820213189374271012581 6369153789973007675814859)
              ·
                refine ⟨9553730684959511513722289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6369153789973007675814859 9553730684959511513722289)
                ·
                  refine ⟨7165298013719633635291717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9553730684959511513722289 7165298013719633635291717)
                  ·
                    refine ⟨1343493377572431306617197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7165298013719633635291717 1343493377572431306617197)
                    ·
                      rfl

theorem cell22_3924666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_3924666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924666 prefixEnd_3924666 := by exact prefixLift 3924666
  have htrace : WordTrace (prefixWord ++ tailWord_3924666) baseStart_3924666 baseEnd_3924666 := by
    simpa [prefixWord, tailWord_3924666, baseEnd_3924666] using wordTrace_append hprefix tailTrace_3924666
  have hstable : (prefixWord ++ tailWord_3924666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924666).length < 2 ^ (prefixWord ++ tailWord_3924666).sum := by decide
  have hdescent : baseEnd_3924666 < baseStart_3924666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924726 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_3924726 : Nat := 118140960795 + 3924726 * 2 ^ 59
def prefixEnd_3924726 : Nat := 4983230072969 + 3 ^ 40 * 3924726 * 2
def baseEnd_3924726 : Nat := 447837972266203716705671

theorem tailTrace_3924726 : CollatzResearch.WordTrace tailWord_3924726 prefixEnd_3924726 447837972266203716705671 := by
  unfold tailWord_3924726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8946657323712216667588127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95431011452930311120940021 8946657323712216667588127)
  ·
    refine ⟨13419985985568325001382191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8946657323712216667588127 13419985985568325001382191)
    ·
      refine ⟨20129978978352487502073287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13419985985568325001382191 20129978978352487502073287)
      ·
        refine ⟨30194968467528731253109931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20129978978352487502073287 30194968467528731253109931)
        ·
          refine ⟨45292452701293096879664897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30194968467528731253109931 45292452701293096879664897)
          ·
            refine ⟨33969339525969822659748673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45292452701293096879664897 33969339525969822659748673)
            ·
              refine ⟨25477004644477366994811505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33969339525969822659748673 25477004644477366994811505)
              ·
                refine ⟨19107753483358025246108629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25477004644477366994811505 19107753483358025246108629)
                ·
                  refine ⟨447837972266203716705671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19107753483358025246108629 447837972266203716705671)
                  ·
                    rfl

theorem cell22_3924726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_3924726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924726 prefixEnd_3924726 := by exact prefixLift 3924726
  have htrace : WordTrace (prefixWord ++ tailWord_3924726) baseStart_3924726 baseEnd_3924726 := by
    simpa [prefixWord, tailWord_3924726, baseEnd_3924726] using wordTrace_append hprefix tailTrace_3924726
  have hstable : (prefixWord ++ tailWord_3924726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924726).length < 2 ^ (prefixWord ++ tailWord_3924726).sum := by decide
  have hdescent : baseEnd_3924726 < baseStart_3924726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924743 : List Nat := [1, 1, 4, 4, 1, 1, 3, 2, 5]
def baseStart_3924743 : Nat := 118140960795 + 3924743 * 2 ^ 59
def prefixEnd_3924743 : Nat := 4983230072969 + 3 ^ 40 * 3924743 * 2
def baseEnd_3924743 : Nat := 447839912082009590813987

theorem tailTrace_3924743 : CollatzResearch.WordTrace tailWord_3924743 prefixEnd_3924743 447839912082009590813987 := by
  unfold tailWord_3924743
  simp only [CollatzResearch.WordTrace]
  refine ⟨143147137220333878584778883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95431424813555919056519255 143147137220333878584778883)
  ·
    refine ⟨214720705830500817877168325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143147137220333878584778883 214720705830500817877168325)
    ·
      refine ⟨40260132343218903351969061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214720705830500817877168325 40260132343218903351969061)
      ·
        refine ⟨7548774814353544378494199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40260132343218903351969061 7548774814353544378494199)
        ·
          refine ⟨11323162221530316567741299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7548774814353544378494199 11323162221530316567741299)
          ·
            refine ⟨16984743332295474851611949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11323162221530316567741299 16984743332295474851611949)
            ·
              refine ⟨6369278749610803069354481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16984743332295474851611949 6369278749610803069354481)
              ·
                refine ⟨4776959062208102302015861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6369278749610803069354481 4776959062208102302015861)
                ·
                  refine ⟨447839912082009590813987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4776959062208102302015861 447839912082009590813987)
                  ·
                    rfl

theorem cell22_3924743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 5].length) (baseStart_3924743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924743 prefixEnd_3924743 := by exact prefixLift 3924743
  have htrace : WordTrace (prefixWord ++ tailWord_3924743) baseStart_3924743 baseEnd_3924743 := by
    simpa [prefixWord, tailWord_3924743, baseEnd_3924743] using wordTrace_append hprefix tailTrace_3924743
  have hstable : (prefixWord ++ tailWord_3924743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924743).length < 2 ^ (prefixWord ++ tailWord_3924743).sum := by decide
  have hdescent : baseEnd_3924743 < baseStart_3924743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924773 : List Nat := [1, 3, 1, 2, 3, 1, 4, 2, 1, 4]
def baseStart_3924773 : Nat := 118140960795 + 3924773 * 2 ^ 59
def prefixEnd_3924773 : Nat := 4983230072969 + 3 ^ 40 * 3924773 * 2
def baseEnd_3924773 : Nat := 1343530005859118694191869

theorem tailTrace_3924773 : CollatzResearch.WordTrace tailWord_3924773 prefixEnd_3924773 1343530005859118694191869 := by
  unfold tailWord_3924773
  simp only [CollatzResearch.WordTrace]
  refine ⟨143148231410225193708370973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95432154273483462472247315 143148231410225193708370973)
  ·
    refine ⟨53680586778834447640639115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143148231410225193708370973 53680586778834447640639115)
    ·
      refine ⟨80520880168251671460958673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53680586778834447640639115 80520880168251671460958673)
      ·
        refine ⟨60390660126188753595719005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80520880168251671460958673 60390660126188753595719005)
        ·
          refine ⟨22646497547320782598394627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60390660126188753595719005 22646497547320782598394627)
          ·
            refine ⟨33969746320981173897591941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22646497547320782598394627 33969746320981173897591941)
            ·
              refine ⟨6369327435183970105798489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33969746320981173897591941 6369327435183970105798489)
              ·
                refine ⟨4776995576387977579348867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6369327435183970105798489 4776995576387977579348867)
                ·
                  refine ⟨7165493364581966369023301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776995576387977579348867 7165493364581966369023301)
                  ·
                    refine ⟨1343530005859118694191869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7165493364581966369023301 1343530005859118694191869)
                    ·
                      rfl

theorem cell22_3924773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_3924773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924773 prefixEnd_3924773 := by exact prefixLift 3924773
  have htrace : WordTrace (prefixWord ++ tailWord_3924773) baseStart_3924773 baseEnd_3924773 := by
    simpa [prefixWord, tailWord_3924773, baseEnd_3924773] using wordTrace_append hprefix tailTrace_3924773
  have hstable : (prefixWord ++ tailWord_3924773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924773).length < 2 ^ (prefixWord ++ tailWord_3924773).sum := by decide
  have hdescent : baseEnd_3924773 < baseStart_3924773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924781 : List Nat := [1, 5, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_3924781 : Nat := 118140960795 + 3924781 * 2 ^ 59
def prefixEnd_3924781 : Nat := 4983230072969 + 3 ^ 40 * 3924781 * 2
def baseEnd_3924781 : Nat := 1343532744422609339991845

theorem tailTrace_3924781 : CollatzResearch.WordTrace tailWord_3924781 prefixEnd_3924781 1343532744422609339991845 := by
  unfold tailWord_3924781
  simp only [CollatzResearch.WordTrace]
  refine ⟨143148523194196211074662197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95432348796130807383108131 143148523194196211074662197)
  ·
    refine ⟨13420174049455894788249581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143148523194196211074662197 13420174049455894788249581)
    ·
      refine ⟨5032565268545960545593593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13420174049455894788249581 5032565268545960545593593)
      ·
        refine ⟨3774423951409470409195195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5032565268545960545593593 3774423951409470409195195)
        ·
          refine ⟨5661635927114205613792793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3774423951409470409195195 5661635927114205613792793)
          ·
            refine ⟨4246226945335654210344595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5661635927114205613792793 4246226945335654210344595)
            ·
              refine ⟨6369340418003481315516893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4246226945335654210344595 6369340418003481315516893)
              ·
                refine ⟨2388502656751305493318835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6369340418003481315516893 2388502656751305493318835)
                ·
                  refine ⟨3582753985126958239978253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2388502656751305493318835 3582753985126958239978253)
                  ·
                    refine ⟨1343532744422609339991845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3582753985126958239978253 1343532744422609339991845)
                    ·
                      rfl

theorem cell22_3924781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_3924781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924781 prefixEnd_3924781 := by exact prefixLift 3924781
  have htrace : WordTrace (prefixWord ++ tailWord_3924781) baseStart_3924781 baseEnd_3924781 := by
    simpa [prefixWord, tailWord_3924781, baseEnd_3924781] using wordTrace_append hprefix tailTrace_3924781
  have hstable : (prefixWord ++ tailWord_3924781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924781).length < 2 ^ (prefixWord ++ tailWord_3924781).sum := by decide
  have hdescent : baseEnd_3924781 < baseStart_3924781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924786 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_3924786 : Nat := 118140960795 + 3924786 * 2 ^ 59
def prefixEnd_3924786 : Nat := 4983230072969 + 3 ^ 40 * 3924786 * 2
def baseEnd_3924786 : Nat := 1343534456024790993616829

theorem tailTrace_3924786 : CollatzResearch.WordTrace tailWord_3924786 prefixEnd_3924786 1343534456024790993616829 := by
  unfold tailWord_3924786
  simp only [CollatzResearch.WordTrace]
  refine ⟨35787176389794524232148553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95432470372785397952396141 35787176389794524232148553)
  ·
    refine ⟨26840382292345893174111415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35787176389794524232148553 26840382292345893174111415)
    ·
      refine ⟨40260573438518839761167123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26840382292345893174111415 40260573438518839761167123)
      ·
        refine ⟨60390860157778259641750685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40260573438518839761167123 60390860157778259641750685)
        ·
          refine ⟨22646572559166847365656507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60390860157778259641750685 22646572559166847365656507)
          ·
            refine ⟨33969858838750271048484761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22646572559166847365656507 33969858838750271048484761)
            ·
              refine ⟨25477394129062703286363571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33969858838750271048484761 25477394129062703286363571)
              ·
                refine ⟨38216091193594054929545357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25477394129062703286363571 38216091193594054929545357)
                ·
                  refine ⟨14331034197597770598579509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38216091193594054929545357 14331034197597770598579509)
                  ·
                    refine ⟨1343534456024790993616829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14331034197597770598579509 1343534456024790993616829)
                    ·
                      rfl

theorem cell22_3924786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_3924786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924786 prefixEnd_3924786 := by exact prefixLift 3924786
  have htrace : WordTrace (prefixWord ++ tailWord_3924786) baseStart_3924786 baseEnd_3924786 := by
    simpa [prefixWord, tailWord_3924786, baseEnd_3924786] using wordTrace_append hprefix tailTrace_3924786
  have hstable : (prefixWord ++ tailWord_3924786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924786).length < 2 ^ (prefixWord ++ tailWord_3924786).sum := by decide
  have hdescent : baseEnd_3924786 < baseStart_3924786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924803 : List Nat := [1, 1, 1, 3, 1, 4, 2, 4, 2, 3]
def baseStart_3924803 : Nat := 118140960795 + 3924803 * 2 ^ 59
def prefixEnd_3924803 : Nat := 4983230072969 + 3 ^ 40 * 3924803 * 2
def baseEnd_3924803 : Nat := 1343540275472208615941777

theorem tailTrace_3924803 : CollatzResearch.WordTrace tailWord_3924803 prefixEnd_3924803 1343540275472208615941777 := by
  unfold tailWord_3924803
  simp only [CollatzResearch.WordTrace]
  refine ⟨143149325600116508831963063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95432883733411005887975375 143149325600116508831963063)
  ·
    refine ⟨214723988400174763247944595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143149325600116508831963063 214723988400174763247944595)
    ·
      refine ⟨322085982600262144871916893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214723988400174763247944595 322085982600262144871916893)
      ·
        refine ⟨120782243475098304326968835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322085982600262144871916893 120782243475098304326968835)
        ·
          refine ⟨181173365212647456490453253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120782243475098304326968835 181173365212647456490453253)
          ·
            refine ⟨33970005977371398091959985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181173365212647456490453253 33970005977371398091959985)
            ·
              refine ⟨25477504483028548568969989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33970005977371398091959985 25477504483028548568969989)
              ·
                refine ⟨4777032090567852856681873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25477504483028548568969989 4777032090567852856681873)
                ·
                  refine ⟨3582774067925889642511405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4777032090567852856681873 3582774067925889642511405)
                  ·
                    refine ⟨1343540275472208615941777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3582774067925889642511405 1343540275472208615941777)
                    ·
                      rfl

theorem cell22_3924803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 3].length) (baseStart_3924803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924803 prefixEnd_3924803 := by exact prefixLift 3924803
  have htrace : WordTrace (prefixWord ++ tailWord_3924803) baseStart_3924803 baseEnd_3924803 := by
    simpa [prefixWord, tailWord_3924803, baseEnd_3924803] using wordTrace_append hprefix tailTrace_3924803
  have hstable : (prefixWord ++ tailWord_3924803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924803).length < 2 ^ (prefixWord ++ tailWord_3924803).sum := by decide
  have hdescent : baseEnd_3924803 < baseStart_3924803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924861 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 7]
def baseStart_3924861 : Nat := 118140960795 + 3924861 * 2 ^ 59
def prefixEnd_3924861 : Nat := 4983230072969 + 3 ^ 40 * 3924861 * 2
def baseEnd_3924861 : Nat := 447853376685838599330533

theorem tailTrace_3924861 : CollatzResearch.WordTrace tailWord_3924861 prefixEnd_3924861 447853376685838599330533 := by
  unfold tailWord_3924861
  simp only [CollatzResearch.WordTrace]
  refine ⟨143151441033906384737574437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95434294022604256491716291 143151441033906384737574437)
  ·
    refine ⟨26840895193857447138295207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143151441033906384737574437 26840895193857447138295207)
    ·
      refine ⟨40261342790786170707442811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26840895193857447138295207 40261342790786170707442811)
      ·
        refine ⟨60392014186179256061164217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40261342790786170707442811 60392014186179256061164217)
        ·
          refine ⟨45294010639634442045873163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60392014186179256061164217 45294010639634442045873163)
          ·
            refine ⟨67941015959451663068809745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45294010639634442045873163 67941015959451663068809745)
            ·
              refine ⟨50955761969588747301607309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67941015959451663068809745 50955761969588747301607309)
              ·
                refine ⟨19108410738595780238102741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50955761969588747301607309 19108410738595780238102741)
                ·
                  refine ⟨447853376685838599330533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19108410738595780238102741 447853376685838599330533)
                  ·
                    rfl

theorem cell22_3924861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_3924861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924861 prefixEnd_3924861 := by exact prefixLift 3924861
  have htrace : WordTrace (prefixWord ++ tailWord_3924861) baseStart_3924861 baseEnd_3924861 := by
    simpa [prefixWord, tailWord_3924861, baseEnd_3924861] using wordTrace_append hprefix tailTrace_3924861
  have hstable : (prefixWord ++ tailWord_3924861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924861).length < 2 ^ (prefixWord ++ tailWord_3924861).sum := by decide
  have hdescent : baseEnd_3924861 < baseStart_3924861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924876 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 1, 7]
def baseStart_3924876 : Nat := 118140960795 + 3924876 * 2 ^ 59
def prefixEnd_3924876 : Nat := 4983230072969 + 3 ^ 40 * 3924876 * 2
def baseEnd_3924876 : Nat := 1343565264864060758866553

theorem tailTrace_3924876 : CollatzResearch.WordTrace tailWord_3924876 prefixEnd_3924876 1343565264864060758866553 := by
  unfold tailWord_3924876
  simp only [CollatzResearch.WordTrace]
  refine ⟨71575994064426021149685241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95434658752568028199580321 71575994064426021149685241)
  ·
    refine ⟨53681995548319515862263931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71575994064426021149685241 53681995548319515862263931)
    ·
      refine ⟨80522993322479273793395897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53681995548319515862263931 80522993322479273793395897)
      ·
        refine ⟨60392244991859455345046923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80522993322479273793395897 60392244991859455345046923)
        ·
          refine ⟨90588367487789183017570385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60392244991859455345046923 90588367487789183017570385)
          ·
            refine ⟨67941275615841887263177789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90588367487789183017570385 67941275615841887263177789)
            ·
              refine ⟨25477978355940707723691671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67941275615841887263177789 25477978355940707723691671)
              ·
                refine ⟨38216967533911061585537507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25477978355940707723691671 38216967533911061585537507)
                ·
                  refine ⟨57325451300866592378306261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38216967533911061585537507 57325451300866592378306261)
                  ·
                    refine ⟨1343565264864060758866553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57325451300866592378306261 1343565264864060758866553)
                    ·
                      rfl

theorem cell22_3924876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_3924876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924876 prefixEnd_3924876 := by exact prefixLift 3924876
  have htrace : WordTrace (prefixWord ++ tailWord_3924876) baseStart_3924876 baseEnd_3924876 := by
    simpa [prefixWord, tailWord_3924876, baseEnd_3924876] using wordTrace_append hprefix tailTrace_3924876
  have hstable : (prefixWord ++ tailWord_3924876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924876).length < 2 ^ (prefixWord ++ tailWord_3924876).sum := by decide
  have hdescent : baseEnd_3924876 < baseStart_3924876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924882 : List Nat := [3, 2, 3, 2, 2, 1, 1, 2, 3, 3]
def baseStart_3924882 : Nat := 118140960795 + 3924882 * 2 ^ 59
def prefixEnd_3924882 : Nat := 4983230072969 + 3 ^ 40 * 3924882 * 2
def baseEnd_3924882 : Nat := 1343567318786678743216535

theorem tailTrace_3924882 : CollatzResearch.WordTrace tailWord_3924882 prefixEnd_3924882 1343567318786678743216535 := by
  unfold tailWord_3924882
  simp only [CollatzResearch.WordTrace]
  refine ⟨35788051741707576331022225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95434804644553536882725933 35788051741707576331022225)
  ·
    refine ⟨26841038806280682248266669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35788051741707576331022225 26841038806280682248266669)
    ·
      refine ⟨10065389552355255843100001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26841038806280682248266669 10065389552355255843100001)
      ·
        refine ⟨7549042164266441882325001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10065389552355255843100001 7549042164266441882325001)
        ·
          refine ⟨5661781623199831411743751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7549042164266441882325001 5661781623199831411743751)
          ·
            refine ⟨8492672434799747117615627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5661781623199831411743751 8492672434799747117615627)
            ·
              refine ⟨12739008652199620676423441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8492672434799747117615627 12739008652199620676423441)
              ·
                refine ⟨9554256489149715507317581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12739008652199620676423441 9554256489149715507317581)
                ·
                  refine ⟨3582846183431143315244093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9554256489149715507317581 3582846183431143315244093)
                  ·
                    refine ⟨1343567318786678743216535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3582846183431143315244093 1343567318786678743216535)
                    ·
                      rfl

theorem cell22_3924882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_3924882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924882 prefixEnd_3924882 := by exact prefixLift 3924882
  have htrace : WordTrace (prefixWord ++ tailWord_3924882) baseStart_3924882 baseEnd_3924882 := by
    simpa [prefixWord, tailWord_3924882, baseEnd_3924882] using wordTrace_append hprefix tailTrace_3924882
  have hstable : (prefixWord ++ tailWord_3924882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924882).length < 2 ^ (prefixWord ++ tailWord_3924882).sum := by decide
  have hdescent : baseEnd_3924882 < baseStart_3924882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924908 : List Nat := [2, 2, 1, 1, 1, 1, 2, 7, 1, 4]
def baseStart_3924908 : Nat := 118140960795 + 3924908 * 2 ^ 59
def prefixEnd_3924908 : Nat := 4983230072969 + 3 ^ 40 * 3924908 * 2
def baseEnd_3924908 : Nat := 1343576219118023342066455

theorem tailTrace_3924908 : CollatzResearch.WordTrace tailWord_3924908 prefixEnd_3924908 1343576219118023342066455 := by
  unfold tailWord_3924908
  simp only [CollatzResearch.WordTrace]
  refine ⟨71576577632368055882267689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95435436843157407843023585 71576577632368055882267689)
  ·
    refine ⟨53682433224276041911700767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71576577632368055882267689 53682433224276041911700767)
    ·
      refine ⟨80523649836414062867551151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53682433224276041911700767 80523649836414062867551151)
      ·
        refine ⟨120785474754621094301326727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80523649836414062867551151 120785474754621094301326727)
        ·
          refine ⟨181178212131931641451990091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120785474754621094301326727 181178212131931641451990091)
          ·
            refine ⟨271767318197897462177985137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181178212131931641451990091 271767318197897462177985137)
            ·
              refine ⟨203825488648423096633488853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271767318197897462177985137 203825488648423096633488853)
              ·
                refine ⟨4777159890197416327347395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 203825488648423096633488853 4777159890197416327347395)
                ·
                  refine ⟨7165739835296124491021093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4777159890197416327347395 7165739835296124491021093)
                  ·
                    refine ⟨1343576219118023342066455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7165739835296124491021093 1343576219118023342066455)
                    ·
                      rfl

theorem cell22_3924908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_3924908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924908 prefixEnd_3924908 := by exact prefixLift 3924908
  have htrace : WordTrace (prefixWord ++ tailWord_3924908) baseStart_3924908 baseEnd_3924908 := by
    simpa [prefixWord, tailWord_3924908, baseEnd_3924908] using wordTrace_append hprefix tailTrace_3924908
  have hstable : (prefixWord ++ tailWord_3924908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924908).length < 2 ^ (prefixWord ++ tailWord_3924908).sum := by decide
  have hdescent : baseEnd_3924908 < baseStart_3924908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924953 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 1, 6]
def baseStart_3924953 : Nat := 118140960795 + 3924953 * 2 ^ 59
def prefixEnd_3924953 : Nat := 4983230072969 + 3 ^ 40 * 3924953 * 2
def baseEnd_3924953 : Nat := 1343591623537658224691317

theorem tailTrace_3924953 : CollatzResearch.WordTrace tailWord_3924953 prefixEnd_3924953 1343591623537658224691317 := by
  unfold tailWord_3924953
  simp only [CollatzResearch.WordTrace]
  refine ⟨143154796549573084449923513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95436531033048722966615675 143154796549573084449923513)
  ·
    refine ⟨107366097412179813337442635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143154796549573084449923513 107366097412179813337442635)
    ·
      refine ⟨161049146118269720006163953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107366097412179813337442635 161049146118269720006163953)
      ·
        refine ⟨120786859588702290004622965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161049146118269720006163953 120786859588702290004622965)
        ·
          refine ⟨11323768086440839687933403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120786859588702290004622965 11323768086440839687933403)
          ·
            refine ⟨16985652129661259531900105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11323768086440839687933403 16985652129661259531900105)
            ·
              refine ⟨12739239097245944648925079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16985652129661259531900105 12739239097245944648925079)
              ·
                refine ⟨19108858645868916973387619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12739239097245944648925079 19108858645868916973387619)
                ·
                  refine ⟨28663287968803375460081429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19108858645868916973387619 28663287968803375460081429)
                  ·
                    refine ⟨1343591623537658224691317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28663287968803375460081429 1343591623537658224691317)
                    ·
                      rfl

theorem cell22_3924953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_3924953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924953 prefixEnd_3924953 := by exact prefixLift 3924953
  have htrace : WordTrace (prefixWord ++ tailWord_3924953) baseStart_3924953 baseEnd_3924953 := by
    simpa [prefixWord, tailWord_3924953, baseEnd_3924953] using wordTrace_append hprefix tailTrace_3924953
  have hstable : (prefixWord ++ tailWord_3924953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924953).length < 2 ^ (prefixWord ++ tailWord_3924953).sum := by decide
  have hdescent : baseEnd_3924953 < baseStart_3924953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924957 : List Nat := [1, 4, 3, 1, 2, 1, 3, 3, 4]
def baseStart_3924957 : Nat := 118140960795 + 3924957 * 2 ^ 59
def prefixEnd_3924957 : Nat := 4983230072969 + 3 ^ 40 * 3924957 * 2
def baseEnd_3924957 : Nat := 447864330939801182530435

theorem tailTrace_3924957 : CollatzResearch.WordTrace tailWord_3924957 prefixEnd_3924957 447864330939801182530435 := by
  unfold tailWord_3924957
  simp only [CollatzResearch.WordTrace]
  refine ⟨143154942441558593133069125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95436628294372395422046083 143154942441558593133069125)
  ·
    refine ⟨26841551707792236212450461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143154942441558593133069125 26841551707792236212450461)
    ·
      refine ⟨10065581890422088579668923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26841551707792236212450461 10065581890422088579668923)
      ·
        refine ⟨15098372835633132869503385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10065581890422088579668923 15098372835633132869503385)
        ·
          refine ⟨11323779626724849652127539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15098372835633132869503385 11323779626724849652127539)
          ·
            refine ⟨16985669440087274478191309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11323779626724849652127539 16985669440087274478191309)
            ·
              refine ⟨6369626040032727929321741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16985669440087274478191309 6369626040032727929321741)
              ·
                refine ⟨2388609765012272973495653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6369626040032727929321741 2388609765012272973495653)
                ·
                  refine ⟨447864330939801182530435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2388609765012272973495653 447864330939801182530435)
                  ·
                    rfl

theorem cell22_3924957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_3924957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924957 prefixEnd_3924957 := by exact prefixLift 3924957
  have htrace : WordTrace (prefixWord ++ tailWord_3924957) baseStart_3924957 baseEnd_3924957 := by
    simpa [prefixWord, tailWord_3924957, baseEnd_3924957] using wordTrace_append hprefix tailTrace_3924957
  have hstable : (prefixWord ++ tailWord_3924957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924957).length < 2 ^ (prefixWord ++ tailWord_3924957).sum := by decide
  have hdescent : baseEnd_3924957 < baseStart_3924957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924970 : List Nat := [3, 1, 3, 1, 2, 3, 1, 2, 2, 4]
def baseStart_3924970 : Nat := 118140960795 + 3924970 * 2 ^ 59
def prefixEnd_3924970 : Nat := 4983230072969 + 3 ^ 40 * 3924970 * 2
def baseEnd_3924970 : Nat := 1343597442985075847016265

theorem tailTrace_3924970 : CollatzResearch.WordTrace tailWord_3924970 prefixEnd_3924970 1343597442985075847016265 := by
  unfold tailWord_3924970
  simp only [CollatzResearch.WordTrace]
  refine ⟨35788854147627874088323091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95436944393674330902194909 35788854147627874088323091)
  ·
    refine ⟨53683281221441811132484637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35788854147627874088323091 53683281221441811132484637)
    ·
      refine ⟨20131230458040679174681739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53683281221441811132484637 20131230458040679174681739)
      ·
        refine ⟨30196845687061018762022609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20131230458040679174681739 30196845687061018762022609)
        ·
          refine ⟨22647634265295764071516957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30196845687061018762022609 22647634265295764071516957)
          ·
            refine ⟨8492862849485911526818859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22647634265295764071516957 8492862849485911526818859)
            ·
              refine ⟨12739294274228867290228289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8492862849485911526818859 12739294274228867290228289)
              ·
                refine ⟨9554470705671650467671217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12739294274228867290228289 9554470705671650467671217)
                ·
                  refine ⟨7165853029253737850753413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9554470705671650467671217 7165853029253737850753413)
                  ·
                    refine ⟨1343597442985075847016265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7165853029253737850753413 1343597442985075847016265)
                    ·
                      rfl

theorem cell22_3924970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_3924970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924970 prefixEnd_3924970 := by exact prefixLift 3924970
  have htrace : WordTrace (prefixWord ++ tailWord_3924970) baseStart_3924970 baseEnd_3924970 := by
    simpa [prefixWord, tailWord_3924970, baseEnd_3924970] using wordTrace_append hprefix tailTrace_3924970
  have hstable : (prefixWord ++ tailWord_3924970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924970).length < 2 ^ (prefixWord ++ tailWord_3924970).sum := by decide
  have hdescent : baseEnd_3924970 < baseStart_3924970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924974 : List Nat := [4, 1, 2, 1, 4, 1, 3, 2, 4]
def baseStart_3924974 : Nat := 118140960795 + 3924974 * 2 ^ 59
def prefixEnd_3924974 : Nat := 4983230072969 + 3 ^ 40 * 3924974 * 2
def baseEnd_3924974 : Nat := 447866270755607056638751

theorem tailTrace_3924974 : CollatzResearch.WordTrace tailWord_3924974 prefixEnd_3924974 447866270755607056638751 := by
  unfold tailWord_3924974
  simp only [CollatzResearch.WordTrace]
  refine ⟨17894445310312125629554747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95437041654998003357625317 17894445310312125629554747)
  ·
    refine ⟨26841667965468188444332121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17894445310312125629554747 26841667965468188444332121)
    ·
      refine ⟨20131250974101141333249091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26841667965468188444332121 20131250974101141333249091)
      ·
        refine ⟨30196876461151711999873637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20131250974101141333249091 30196876461151711999873637)
        ·
          refine ⟨5661914336465945999976307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30196876461151711999873637 5661914336465945999976307)
          ·
            refine ⟨8492871504698918999964461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5661914336465945999976307 8492871504698918999964461)
            ·
              refine ⟨3184826814262094624986673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8492871504698918999964461 3184826814262094624986673)
              ·
                refine ⟨2388620110696570968740005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3184826814262094624986673 2388620110696570968740005)
                ·
                  refine ⟨447866270755607056638751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2388620110696570968740005 447866270755607056638751)
                  ·
                    rfl

theorem cell22_3924974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_3924974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924974 prefixEnd_3924974 := by exact prefixLift 3924974
  have htrace : WordTrace (prefixWord ++ tailWord_3924974) baseStart_3924974 baseEnd_3924974 := by
    simpa [prefixWord, tailWord_3924974, baseEnd_3924974] using wordTrace_append hprefix tailTrace_3924974
  have hstable : (prefixWord ++ tailWord_3924974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924974).length < 2 ^ (prefixWord ++ tailWord_3924974).sum := by decide
  have hdescent : baseEnd_3924974 < baseStart_3924974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924980 : List Nat := [2, 6, 2, 1, 2, 1, 2, 1, 5]
def baseStart_3924980 : Nat := 118140960795 + 3924980 * 2 ^ 59
def prefixEnd_3924980 : Nat := 4983230072969 + 3 ^ 40 * 3924980 * 2
def baseEnd_3924980 : Nat := 447866955396479718088745

theorem tailTrace_3924980 : CollatzResearch.WordTrace tailWord_3924980 prefixEnd_3924980 447866955396479718088745 := by
  unfold tailWord_3924980
  simp only [CollatzResearch.WordTrace]
  refine ⟨71577890660237634030578197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95437187546983512040770929 71577890660237634030578197)
  ·
    refine ⟨3355213624698639095183353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71577890660237634030578197 3355213624698639095183353)
    ·
      refine ⟨2516410218523979321387515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3355213624698639095183353 2516410218523979321387515)
      ·
        refine ⟨3774615327785968982081273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2516410218523979321387515 3774615327785968982081273)
        ·
          refine ⟨2830961495839476736560955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3774615327785968982081273 2830961495839476736560955)
          ·
            refine ⟨4246442243759215104841433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830961495839476736560955 4246442243759215104841433)
            ·
              refine ⟨3184831682819411328631075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4246442243759215104841433 3184831682819411328631075)
              ·
                refine ⟨4777247524229116992946613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3184831682819411328631075 4777247524229116992946613)
                ·
                  refine ⟨447866955396479718088745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4777247524229116992946613 447866955396479718088745)
                  ·
                    rfl

theorem cell22_3924980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_3924980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3924980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3924980 prefixEnd_3924980 := by exact prefixLift 3924980
  have htrace : WordTrace (prefixWord ++ tailWord_3924980) baseStart_3924980 baseEnd_3924980 := by
    simpa [prefixWord, tailWord_3924980, baseEnd_3924980] using wordTrace_append hprefix tailTrace_3924980
  have hstable : (prefixWord ++ tailWord_3924980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924980).length < 2 ^ (prefixWord ++ tailWord_3924980).sum := by decide
  have hdescent : baseEnd_3924980 < baseStart_3924980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925075 : List Nat := [1, 1, 1, 2, 1, 1, 2, 9, 4]
def baseStart_3925075 : Nat := 118140960795 + 3925075 * 2 ^ 59
def prefixEnd_3925075 : Nat := 4983230072969 + 3 ^ 40 * 3925075 * 2
def baseEnd_3925075 : Nat := 447877795543630191046981

theorem tailTrace_3925075 : CollatzResearch.WordTrace tailWord_3925075 prefixEnd_3925075 447877795543630191046981 := by
  unfold tailWord_3925075
  simp only [CollatzResearch.WordTrace]
  refine ⟨143159246255131099285864679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95439497503420732857243119 143159246255131099285864679)
  ·
    refine ⟨214738869382696648928797019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143159246255131099285864679 214738869382696648928797019)
    ·
      refine ⟨322108304074044973393195529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214738869382696648928797019 322108304074044973393195529)
      ·
        refine ⟨241581228055533730044896647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322108304074044973393195529 241581228055533730044896647)
        ·
          refine ⟨362371842083300595067344971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241581228055533730044896647 362371842083300595067344971)
          ·
            refine ⟨543557763124950892601017457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362371842083300595067344971 543557763124950892601017457)
            ·
              refine ⟨407668322343713169450763093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543557763124950892601017457 407668322343713169450763093)
              ·
                refine ⟨2388681576232694352250565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 407668322343713169450763093 2388681576232694352250565)
                ·
                  refine ⟨447877795543630191046981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2388681576232694352250565 447877795543630191046981)
                  ·
                    rfl

theorem cell22_3925075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 4].length) (baseStart_3925075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925075 prefixEnd_3925075 := by exact prefixLift 3925075
  have htrace : WordTrace (prefixWord ++ tailWord_3925075) baseStart_3925075 baseEnd_3925075 := by
    simpa [prefixWord, tailWord_3925075, baseEnd_3925075] using wordTrace_append hprefix tailTrace_3925075
  have hstable : (prefixWord ++ tailWord_3925075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925075).length < 2 ^ (prefixWord ++ tailWord_3925075).sum := by decide
  have hdescent : baseEnd_3925075 < baseStart_3925075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925103 : List Nat := [1, 1, 2, 1, 3, 3, 2, 9]
def baseStart_3925103 : Nat := 118140960795 + 3925103 * 2 ^ 59
def prefixEnd_3925103 : Nat := 4983230072969 + 3 ^ 40 * 3925103 * 2
def baseEnd_3925103 : Nat := 149293663511456425937873

theorem tailTrace_3925103 : CollatzResearch.WordTrace tailWord_3925103 prefixEnd_3925103 149293663511456425937873 := by
  unfold tailWord_3925103
  simp only [CollatzResearch.WordTrace]
  refine ⟨143160267499029660067883963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95440178332686440045255975 143160267499029660067883963)
  ·
    refine ⟨214740401248544490101825945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143160267499029660067883963 214740401248544490101825945)
    ·
      refine ⟨161055300936408367576369459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214740401248544490101825945 161055300936408367576369459)
      ·
        refine ⟨241582951404612551364554189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161055300936408367576369459 241582951404612551364554189)
        ·
          refine ⟨90593606776729706761707821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241582951404612551364554189 90593606776729706761707821)
          ·
            refine ⟨33972602541273640035640433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90593606776729706761707821 33972602541273640035640433)
            ·
              refine ⟨25479451905955230026730325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33972602541273640035640433 25479451905955230026730325)
              ·
                refine ⟨149293663511456425937873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25479451905955230026730325 149293663511456425937873)
                ·
                  rfl

theorem cell22_3925103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 9].length) (baseStart_3925103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925103 prefixEnd_3925103 := by exact prefixLift 3925103
  have htrace : WordTrace (prefixWord ++ tailWord_3925103) baseStart_3925103 baseEnd_3925103 := by
    simpa [prefixWord, tailWord_3925103, baseEnd_3925103] using wordTrace_append hprefix tailTrace_3925103
  have hstable : (prefixWord ++ tailWord_3925103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925103).length < 2 ^ (prefixWord ++ tailWord_3925103).sum := by decide
  have hdescent : baseEnd_3925103 < baseStart_3925103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925120 : List Nat := [2, 1, 1, 2, 1, 3, 6, 6]
def baseStart_3925120 : Nat := 118140960795 + 3925120 * 2 ^ 59
def prefixEnd_3925120 : Nat := 4983230072969 + 3 ^ 40 * 3925120 * 2
def baseEnd_3925120 : Nat := 149294310116725050640645

theorem tailTrace_3925120 : CollatzResearch.WordTrace tailWord_3925120 prefixEnd_3925120 149294310116725050640645 := by
  unfold tailWord_3925120
  simp only [CollatzResearch.WordTrace]
  refine ⟨71580443769984035985626407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95440591693312047980835209 71580443769984035985626407)
  ·
    refine ⟨107370665654976053978439611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71580443769984035985626407 107370665654976053978439611)
    ·
      refine ⟨161055998482464080967659417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107370665654976053978439611 161055998482464080967659417)
      ·
        refine ⟨120791998861848060725744563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161055998482464080967659417 120791998861848060725744563)
        ·
          refine ⟨181187998292772091088616845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120791998861848060725744563 181187998292772091088616845)
          ·
            refine ⟨67945499359789534158231317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181187998292772091088616845 67945499359789534158231317)
            ·
              refine ⟨3184945282490134413667093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67945499359789534158231317 3184945282490134413667093)
              ·
                refine ⟨149294310116725050640645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3184945282490134413667093 149294310116725050640645)
                ·
                  rfl

theorem cell22_3925120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 6].length) (baseStart_3925120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925120 prefixEnd_3925120 := by exact prefixLift 3925120
  have htrace : WordTrace (prefixWord ++ tailWord_3925120) baseStart_3925120 baseEnd_3925120 := by
    simpa [prefixWord, tailWord_3925120, baseEnd_3925120] using wordTrace_append hprefix tailTrace_3925120
  have hstable : (prefixWord ++ tailWord_3925120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925120).length < 2 ^ (prefixWord ++ tailWord_3925120).sum := by decide
  have hdescent : baseEnd_3925120 < baseStart_3925120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925210 : List Nat := [3, 1, 1, 2, 2, 1, 1, 5, 6]
def baseStart_3925210 : Nat := 118140960795 + 3925210 * 2 ^ 59
def prefixEnd_3925210 : Nat := 4983230072969 + 3 ^ 40 * 3925210 * 2
def baseEnd_3925210 : Nat := 447893199963265073671843

theorem tailTrace_3925210 : CollatzResearch.WordTrace tailWord_3925210 prefixEnd_3925210 447893199963265073671843 := by
  unfold tailWord_3925210
  simp only [CollatzResearch.WordTrace]
  refine ⟨35791042527410504335507271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95442780073094678228019389 35791042527410504335507271)
  ·
    refine ⟨53686563791115756503260907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35791042527410504335507271 53686563791115756503260907)
    ·
      refine ⟨80529845686673634754891361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53686563791115756503260907 80529845686673634754891361)
      ·
        refine ⟨60397384265005226066168521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80529845686673634754891361 60397384265005226066168521)
        ·
          refine ⟨45298038198753919549626391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60397384265005226066168521 45298038198753919549626391)
          ·
            refine ⟨67947057298130879324439587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45298038198753919549626391 67947057298130879324439587)
            ·
              refine ⟨101920585947196318986659381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67947057298130879324439587 101920585947196318986659381)
              ·
                refine ⟨9555054932549654904999317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101920585947196318986659381 9555054932549654904999317)
                ·
                  refine ⟨447893199963265073671843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9555054932549654904999317 447893199963265073671843)
                  ·
                    rfl

theorem cell22_3925210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_3925210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925210 prefixEnd_3925210 := by exact prefixLift 3925210
  have htrace : WordTrace (prefixWord ++ tailWord_3925210) baseStart_3925210 baseEnd_3925210 := by
    simpa [prefixWord, tailWord_3925210, baseEnd_3925210] using wordTrace_append hprefix tailTrace_3925210
  have hstable : (prefixWord ++ tailWord_3925210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925210).length < 2 ^ (prefixWord ++ tailWord_3925210).sum := by decide
  have hdescent : baseEnd_3925210 < baseStart_3925210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925242 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 4, 3]
def baseStart_3925242 : Nat := 118140960795 + 3925242 * 2 ^ 59
def prefixEnd_3925242 : Nat := 4983230072969 + 3 ^ 40 * 3925242 * 2
def baseEnd_3925242 : Nat := 1343690554143757804215431

theorem tailTrace_3925242 : CollatzResearch.WordTrace tailWord_3925242 prefixEnd_3925242 1343690554143757804215431 := by
  unfold tailWord_3925242
  simp only [CollatzResearch.WordTrace]
  refine ⟨35791334311381521701798495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95443558163684057871462653 35791334311381521701798495)
  ·
    refine ⟨53687001467072282552697743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35791334311381521701798495 53687001467072282552697743)
    ·
      refine ⟨80530502200608423829046615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53687001467072282552697743 80530502200608423829046615)
      ·
        refine ⟨120795753300912635743569923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80530502200608423829046615 120795753300912635743569923)
        ·
          refine ⟨181193629951368953615354885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120795753300912635743569923 181193629951368953615354885)
          ·
            refine ⟨33973805615881678802879041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181193629951368953615354885 33973805615881678802879041)
            ·
              refine ⟨25480354211911259102159281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33973805615881678802879041 25480354211911259102159281)
              ·
                refine ⟨19110265658933444326619461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25480354211911259102159281 19110265658933444326619461)
                ·
                  refine ⟨3583174811050020811241149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19110265658933444326619461 3583174811050020811241149)
                  ·
                    refine ⟨1343690554143757804215431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3583174811050020811241149 1343690554143757804215431)
                    ·
                      rfl

theorem cell22_3925242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_3925242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925242 prefixEnd_3925242 := by exact prefixLift 3925242
  have htrace : WordTrace (prefixWord ++ tailWord_3925242) baseStart_3925242 baseEnd_3925242 := by
    simpa [prefixWord, tailWord_3925242, baseEnd_3925242] using wordTrace_append hprefix tailTrace_3925242
  have hstable : (prefixWord ++ tailWord_3925242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925242).length < 2 ^ (prefixWord ++ tailWord_3925242).sum := by decide
  have hdescent : baseEnd_3925242 < baseStart_3925242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925246 : List Nat := [4, 2, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_3925246 : Nat := 118140960795 + 3925246 * 2 ^ 59
def prefixEnd_3925246 : Nat := 4983230072969 + 3 ^ 40 * 3925246 * 2
def baseEnd_3925246 : Nat := 1343691923425503127115419

theorem tailTrace_3925246 : CollatzResearch.WordTrace tailWord_3925246 prefixEnd_3925246 1343691923425503127115419 := by
  unfold tailWord_3925246
  simp only [CollatzResearch.WordTrace]
  refine ⟨17895685392188949436292449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95443655425007730326893061 17895685392188949436292449)
  ·
    refine ⟨13421764044141712077219337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17895685392188949436292449 13421764044141712077219337)
    ·
      refine ⟨10066323033106284057914503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13421764044141712077219337 10066323033106284057914503)
      ·
        refine ⟨15099484549659426086871755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10066323033106284057914503 15099484549659426086871755)
        ·
          refine ⟨22649226824489139130307633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15099484549659426086871755 22649226824489139130307633)
          ·
            refine ⟨16986920118366854347730725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22649226824489139130307633 16986920118366854347730725)
            ·
              refine ⟨3185047522193785190199511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16986920118366854347730725 3185047522193785190199511)
              ·
                refine ⟨4777571283290677785299267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3185047522193785190199511 4777571283290677785299267)
                ·
                  refine ⟨7166356924936016677948901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4777571283290677785299267 7166356924936016677948901)
                  ·
                    refine ⟨1343691923425503127115419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7166356924936016677948901 1343691923425503127115419)
                    ·
                      rfl

theorem cell22_3925246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_3925246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925246 prefixEnd_3925246 := by exact prefixLift 3925246
  have htrace : WordTrace (prefixWord ++ tailWord_3925246) baseStart_3925246 baseEnd_3925246 := by
    simpa [prefixWord, tailWord_3925246, baseEnd_3925246] using wordTrace_append hprefix tailTrace_3925246
  have hstable : (prefixWord ++ tailWord_3925246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925246).length < 2 ^ (prefixWord ++ tailWord_3925246).sum := by decide
  have hdescent : baseEnd_3925246 < baseStart_3925246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925259 : List Nat := [1, 1, 1, 1, 5, 3, 3, 2, 2, 3]
def baseStart_3925259 : Nat := 118140960795 + 3925259 * 2 ^ 59
def prefixEnd_3925259 : Nat := 4983230072969 + 3 ^ 40 * 3925259 * 2
def baseEnd_3925259 : Nat := 1343696373591175426540379

theorem tailTrace_3925259 : CollatzResearch.WordTrace tailWord_3925259 prefixEnd_3925259 1343696373591175426540379 := by
  unfold tailWord_3925259
  simp only [CollatzResearch.WordTrace]
  refine ⟨143165957286464498710562831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95443971524309665807041887 143165957286464498710562831)
  ·
    refine ⟨214748935929696748065844247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143165957286464498710562831 214748935929696748065844247)
    ·
      refine ⟨322123403894545122098766371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214748935929696748065844247 322123403894545122098766371)
      ·
        refine ⟨483185105841817683148149557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322123403894545122098766371 483185105841817683148149557)
        ·
          refine ⟨45298603672670407795139021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 483185105841817683148149557 45298603672670407795139021)
          ·
            refine ⟨16986976377251402923177133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45298603672670407795139021 16986976377251402923177133)
            ·
              refine ⟨6370116141469276096191425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16986976377251402923177133 6370116141469276096191425)
              ·
                refine ⟨4777587106101957072143569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6370116141469276096191425 4777587106101957072143569)
                ·
                  refine ⟨3583190329576467804107677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4777587106101957072143569 3583190329576467804107677)
                  ·
                    refine ⟨1343696373591175426540379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3583190329576467804107677 1343696373591175426540379)
                    ·
                      rfl

theorem cell22_3925259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 3].length) (baseStart_3925259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925259 prefixEnd_3925259 := by exact prefixLift 3925259
  have htrace : WordTrace (prefixWord ++ tailWord_3925259) baseStart_3925259 baseEnd_3925259 := by
    simpa [prefixWord, tailWord_3925259, baseEnd_3925259] using wordTrace_append hprefix tailTrace_3925259
  have hstable : (prefixWord ++ tailWord_3925259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925259).length < 2 ^ (prefixWord ++ tailWord_3925259).sum := by decide
  have hdescent : baseEnd_3925259 < baseStart_3925259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925332 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_3925332 : Nat := 118140960795 + 3925332 * 2 ^ 59
def prefixEnd_3925332 : Nat := 4983230072969 + 3 ^ 40 * 3925332 * 2
def baseEnd_3925332 : Nat := 1343721362983027569465155

theorem tailTrace_3925332 : CollatzResearch.WordTrace tailWord_3925332 prefixEnd_3925332 1343721362983027569465155 := by
  unfold tailWord_3925332
  simp only [CollatzResearch.WordTrace]
  refine ⟨71584309907600016088985125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95445746543466688118646833 71584309907600016088985125)
  ·
    refine ⟨13422058107675003016684711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71584309907600016088985125 13422058107675003016684711)
    ·
      refine ⟨20133087161512504525027067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13422058107675003016684711 20133087161512504525027067)
      ·
        refine ⟨30199630742268756787540601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20133087161512504525027067 30199630742268756787540601)
        ·
          refine ⟨22649723056701567590655451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30199630742268756787540601 22649723056701567590655451)
          ·
            refine ⟨33974584585052351385983177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22649723056701567590655451 33974584585052351385983177)
            ·
              refine ⟨25480938438789263539487383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33974584585052351385983177 25480938438789263539487383)
              ·
                refine ⟨38221407658183895309231075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25480938438789263539487383 38221407658183895309231075)
                ·
                  refine ⟨57332111487275842963846613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38221407658183895309231075 57332111487275842963846613)
                  ·
                    refine ⟨1343721362983027569465155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57332111487275842963846613 1343721362983027569465155)
                    ·
                      rfl

theorem cell22_3925332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_3925332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925332 prefixEnd_3925332 := by exact prefixLift 3925332
  have htrace : WordTrace (prefixWord ++ tailWord_3925332) baseStart_3925332 baseEnd_3925332 := by
    simpa [prefixWord, tailWord_3925332, baseEnd_3925332] using wordTrace_append hprefix tailTrace_3925332
  have hstable : (prefixWord ++ tailWord_3925332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925332).length < 2 ^ (prefixWord ++ tailWord_3925332).sum := by decide
  have hdescent : baseEnd_3925332 < baseStart_3925332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925469 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 7]
def baseStart_3925469 : Nat := 118140960795 + 3925469 * 2 ^ 59
def prefixEnd_3925469 : Nat := 4983230072969 + 3 ^ 40 * 3925469 * 2
def baseEnd_3925469 : Nat := 447922753627601626263245

theorem tailTrace_3925469 : CollatzResearch.WordTrace tailWord_3925469 prefixEnd_3925469 447922753627601626263245 := by
  unfold tailWord_3925469
  simp only [CollatzResearch.WordTrace]
  refine ⟨143173616615703704575707461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95449077743802469717138307 143173616615703704575707461)
  ·
    refine ⟨26845053115444444607945149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143173616615703704575707461 26845053115444444607945149)
    ·
      refine ⟨10066894918291666727979431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26845053115444444607945149 10066894918291666727979431)
      ·
        refine ⟨15100342377437500091969147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10066894918291666727979431 15100342377437500091969147)
        ·
          refine ⟨22650513566156250137953721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15100342377437500091969147 22650513566156250137953721)
          ·
            refine ⟨16987885174617187603465291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22650513566156250137953721 16987885174617187603465291)
            ·
              refine ⟨25481827761925781405197937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16987885174617187603465291 25481827761925781405197937)
              ·
                refine ⟨19111370821444336053898453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25481827761925781405197937 19111370821444336053898453)
                ·
                  refine ⟨447922753627601626263245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19111370821444336053898453 447922753627601626263245)
                  ·
                    rfl

theorem cell22_3925469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_3925469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925469 prefixEnd_3925469 := by exact prefixLift 3925469
  have htrace : WordTrace (prefixWord ++ tailWord_3925469) baseStart_3925469 baseEnd_3925469 := by
    simpa [prefixWord, tailWord_3925469, baseEnd_3925469] using wordTrace_append hprefix tailTrace_3925469
  have hstable : (prefixWord ++ tailWord_3925469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925469).length < 2 ^ (prefixWord ++ tailWord_3925469).sum := by decide
  have hdescent : baseEnd_3925469 < baseStart_3925469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925473 : List Nat := [1, 2, 3, 1, 2, 3, 3, 3, 1, 3]
def baseStart_3925473 : Nat := 118140960795 + 3925473 * 2 ^ 59
def prefixEnd_3925473 : Nat := 4983230072969 + 3 ^ 40 * 3925473 * 2
def baseEnd_3925473 : Nat := 1343769630164550201689723

theorem tailTrace_3925473 : CollatzResearch.WordTrace tailWord_3925473 prefixEnd_3925473 1343769630164550201689723 := by
  unfold tailWord_3925473
  simp only [CollatzResearch.WordTrace]
  refine ⟨143173762507689213258853073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95449175005126142172568715 143173762507689213258853073)
  ·
    refine ⟨107380321880766909944139805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143173762507689213258853073 107380321880766909944139805)
    ·
      refine ⟨40267620705287591229052427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107380321880766909944139805 40267620705287591229052427)
      ·
        refine ⟨60401431057931386843578641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40267620705287591229052427 60401431057931386843578641)
        ·
          refine ⟨45301073293448540132683981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60401431057931386843578641 45301073293448540132683981)
          ·
            refine ⟨16987902485043202549756493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45301073293448540132683981 16987902485043202549756493)
            ·
              refine ⟨6370463431891200956158685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16987902485043202549756493 6370463431891200956158685)
              ·
                refine ⟨2388923786959200358559507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6370463431891200956158685 2388923786959200358559507)
                ·
                  refine ⟨3583385680438800537839261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2388923786959200358559507 3583385680438800537839261)
                  ·
                    refine ⟨1343769630164550201689723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3583385680438800537839261 1343769630164550201689723)
                    ·
                      rfl

theorem cell22_3925473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_3925473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925473 prefixEnd_3925473 := by exact prefixLift 3925473
  have htrace : WordTrace (prefixWord ++ tailWord_3925473) baseStart_3925473 baseEnd_3925473 := by
    simpa [prefixWord, tailWord_3925473, baseEnd_3925473] using wordTrace_append hprefix tailTrace_3925473
  have hstable : (prefixWord ++ tailWord_3925473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925473).length < 2 ^ (prefixWord ++ tailWord_3925473).sum := by decide
  have hdescent : baseEnd_3925473 < baseStart_3925473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925516 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 3, 4]
def baseStart_3925516 : Nat := 118140960795 + 3925516 * 2 ^ 59
def prefixEnd_3925516 : Nat := 4983230072969 + 3 ^ 40 * 3925516 * 2
def baseEnd_3925516 : Nat := 1343784349943312422864591

theorem tailTrace_3925516 : CollatzResearch.WordTrace tailWord_3925516 prefixEnd_3925516 1343784349943312422864591 := by
  unfold tailWord_3925516
  simp only [CollatzResearch.WordTrace]
  refine ⟨71587665423266715801334201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95450220564355621068445601 71587665423266715801334201)
  ·
    refine ⟨53690749067450036851000651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71587665423266715801334201 53690749067450036851000651)
    ·
      refine ⟨80536123601175055276500977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53690749067450036851000651 80536123601175055276500977)
      ·
        refine ⟨60402092700881291457375733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80536123601175055276500977 60402092700881291457375733)
        ·
          refine ⟨5662696190707621074128975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60402092700881291457375733 5662696190707621074128975)
          ·
            refine ⟨8494044286061431611193463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5662696190707621074128975 8494044286061431611193463)
            ·
              refine ⟨12741066429092147416790195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8494044286061431611193463 12741066429092147416790195)
              ·
                refine ⟨19111599643638221125185293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12741066429092147416790195 19111599643638221125185293)
                ·
                  refine ⟨7166849866364332921944485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19111599643638221125185293 7166849866364332921944485)
                  ·
                    refine ⟨1343784349943312422864591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7166849866364332921944485 1343784349943312422864591)
                    ·
                      rfl

theorem cell22_3925516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_3925516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925516 prefixEnd_3925516 := by exact prefixLift 3925516
  have htrace : WordTrace (prefixWord ++ tailWord_3925516) baseStart_3925516 baseEnd_3925516 := by
    simpa [prefixWord, tailWord_3925516, baseEnd_3925516] using wordTrace_append hprefix tailTrace_3925516
  have hstable : (prefixWord ++ tailWord_3925516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925516).length < 2 ^ (prefixWord ++ tailWord_3925516).sum := by decide
  have hdescent : baseEnd_3925516 < baseStart_3925516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925533 : List Nat := [1, 4, 2, 2, 1, 1, 5, 1, 1, 4]
def baseStart_3925533 : Nat := 118140960795 + 3925533 * 2 ^ 59
def prefixEnd_3925533 : Nat := 4983230072969 + 3 ^ 40 * 3925533 * 2
def baseEnd_3925533 : Nat := 1343790169390730045189539

theorem tailTrace_3925533 : CollatzResearch.WordTrace tailWord_3925533 prefixEnd_3925533 1343790169390730045189539 := by
  unfold tailWord_3925533
  simp only [CollatzResearch.WordTrace]
  refine ⟨143175950887471843506037253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95450633924981229004024835 143175950887471843506037253)
  ·
    refine ⟨26845490791400970657381985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143175950887471843506037253 26845490791400970657381985)
    ·
      refine ⟨20134118093550727993036489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26845490791400970657381985 20134118093550727993036489)
      ·
        refine ⟨15100588570163045994777367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20134118093550727993036489 15100588570163045994777367)
        ·
          refine ⟨22650882855244568992166051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15100588570163045994777367 22650882855244568992166051)
          ·
            refine ⟨33976324282866853488249077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22650882855244568992166051 33976324282866853488249077)
            ·
              refine ⟨3185280401518767514523351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33976324282866853488249077 3185280401518767514523351)
              ·
                refine ⟨4777920602278151271785027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3185280401518767514523351 4777920602278151271785027)
                ·
                  refine ⟨7166880903417226907677541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4777920602278151271785027 7166880903417226907677541)
                  ·
                    refine ⟨1343790169390730045189539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7166880903417226907677541 1343790169390730045189539)
                    ·
                      rfl

theorem cell22_3925533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_3925533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925533 prefixEnd_3925533 := by exact prefixLift 3925533
  have htrace : WordTrace (prefixWord ++ tailWord_3925533) baseStart_3925533 baseEnd_3925533 := by
    simpa [prefixWord, tailWord_3925533, baseEnd_3925533] using wordTrace_append hprefix tailTrace_3925533
  have hstable : (prefixWord ++ tailWord_3925533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925533).length < 2 ^ (prefixWord ++ tailWord_3925533).sum := by decide
  have hdescent : baseEnd_3925533 < baseStart_3925533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925559 : List Nat := [1, 1, 3, 1, 2, 4, 3, 7]
def baseStart_3925559 : Nat := 118140960795 + 3925559 * 2 ^ 59
def prefixEnd_3925559 : Nat := 4983230072969 + 3 ^ 40 * 3925559 * 2
def baseEnd_3925559 : Nat := 149311007746897182671051

theorem tailTrace_3925559 : CollatzResearch.WordTrace tailWord_3925559 prefixEnd_3925559 149311007746897182671051 := by
  unfold tailWord_3925559
  simp only [CollatzResearch.WordTrace]
  refine ⟨143176899185377649946483731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95451266123585099964322487 143176899185377649946483731)
  ·
    refine ⟨214765348778066474919725597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143176899185377649946483731 214765348778066474919725597)
    ·
      refine ⟨80537005791774928094897099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214765348778066474919725597 80537005791774928094897099)
      ·
        refine ⟨120805508687662392142345649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80537005791774928094897099 120805508687662392142345649)
        ·
          refine ⟨90604131515746794106759237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120805508687662392142345649 90604131515746794106759237)
          ·
            refine ⟨16988274659202523895017357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90604131515746794106759237 16988274659202523895017357)
            ·
              refine ⟨6370602997200946460631509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16988274659202523895017357 6370602997200946460631509)
              ·
                refine ⟨149311007746897182671051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6370602997200946460631509 149311007746897182671051)
                ·
                  rfl

theorem cell22_3925559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 7].length) (baseStart_3925559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925559 prefixEnd_3925559 := by exact prefixLift 3925559
  have htrace : WordTrace (prefixWord ++ tailWord_3925559) baseStart_3925559 baseEnd_3925559 := by
    simpa [prefixWord, tailWord_3925559, baseEnd_3925559] using wordTrace_append hprefix tailTrace_3925559
  have hstable : (prefixWord ++ tailWord_3925559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925559).length < 2 ^ (prefixWord ++ tailWord_3925559).sum := by decide
  have hdescent : baseEnd_3925559 < baseStart_3925559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925608 : List Nat := [2, 1, 4, 3, 1, 1, 1, 3, 3, 3]
def baseStart_3925608 : Nat := 118140960795 + 3925608 * 2 ^ 59
def prefixEnd_3925608 : Nat := 4983230072969 + 3 ^ 40 * 3925608 * 2
def baseEnd_3925608 : Nat := 1343815843423454849564309

theorem tailTrace_3925608 : CollatzResearch.WordTrace tailWord_3925608 prefixEnd_3925608 1343815843423454849564309 := by
  unfold tailWord_3925608
  simp only [CollatzResearch.WordTrace]
  refine ⟨71589343181100065657508739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95452457574800087543344985 71589343181100065657508739)
  ·
    refine ⟨107384014771650098486263109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71589343181100065657508739 107384014771650098486263109)
    ·
      refine ⟨20134502769684393466174333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107384014771650098486263109 20134502769684393466174333)
      ·
        refine ⟨7550438538631647549815375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20134502769684393466174333 7550438538631647549815375)
        ·
          refine ⟨11325657807947471324723063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7550438538631647549815375 11325657807947471324723063)
          ·
            refine ⟨16988486711921206987084595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11325657807947471324723063 16988486711921206987084595)
            ·
              refine ⟨25482730067881810480626893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16988486711921206987084595 25482730067881810480626893)
              ·
                refine ⟨9556023775455678930235085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25482730067881810480626893 9556023775455678930235085)
                ·
                  refine ⟨3583508915795879598838157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9556023775455678930235085 3583508915795879598838157)
                  ·
                    refine ⟨1343815843423454849564309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3583508915795879598838157 1343815843423454849564309)
                    ·
                      rfl

theorem cell22_3925608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_3925608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925608 prefixEnd_3925608 := by exact prefixLift 3925608
  have htrace : WordTrace (prefixWord ++ tailWord_3925608) baseStart_3925608 baseEnd_3925608 := by
    simpa [prefixWord, tailWord_3925608, baseEnd_3925608] using wordTrace_append hprefix tailTrace_3925608
  have hstable : (prefixWord ++ tailWord_3925608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925608).length < 2 ^ (prefixWord ++ tailWord_3925608).sum := by decide
  have hdescent : baseEnd_3925608 < baseStart_3925608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925642 : List Nat := [3, 1, 2, 3, 2, 3, 1, 3, 1, 3]
def baseStart_3925642 : Nat := 118140960795 + 3925642 * 2 ^ 59
def prefixEnd_3925642 : Nat := 4983230072969 + 3 ^ 40 * 3925642 * 2
def baseEnd_3925642 : Nat := 1343827482318290094214205

theorem tailTrace_3925642 : CollatzResearch.WordTrace tailWord_3925642 prefixEnd_3925642 1343827482318290094214205 := by
  unfold tailWord_3925642
  simp only [CollatzResearch.WordTrace]
  refine ⟨35794981611019238780438795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95453284296051303414503453 35794981611019238780438795)
  ·
    refine ⟨53692472416528858170658193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35794981611019238780438795 53692472416528858170658193)
    ·
      refine ⟨40269354312396643627993645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53692472416528858170658193 40269354312396643627993645)
      ·
        refine ⟨15101007867148741360497617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40269354312396643627993645 15101007867148741360497617)
        ·
          refine ⟨11325755900361556020373213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15101007867148741360497617 11325755900361556020373213)
          ·
            refine ⟨4247158462635583507639955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11325755900361556020373213 4247158462635583507639955)
            ·
              refine ⟨6370737693953375261459933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4247158462635583507639955 6370737693953375261459933)
              ·
                refine ⟨2389026635232515723047475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6370737693953375261459933 2389026635232515723047475)
                ·
                  refine ⟨3583539952848773584571213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2389026635232515723047475 3583539952848773584571213)
                  ·
                    refine ⟨1343827482318290094214205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3583539952848773584571213 1343827482318290094214205)
                    ·
                      rfl

theorem cell22_3925642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_3925642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925642 prefixEnd_3925642 := by exact prefixLift 3925642
  have htrace : WordTrace (prefixWord ++ tailWord_3925642) baseStart_3925642 baseEnd_3925642 := by
    simpa [prefixWord, tailWord_3925642, baseEnd_3925642] using wordTrace_append hprefix tailTrace_3925642
  have hstable : (prefixWord ++ tailWord_3925642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925642).length < 2 ^ (prefixWord ++ tailWord_3925642).sum := by decide
  have hdescent : baseEnd_3925642 < baseStart_3925642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925672 : List Nat := [2, 1, 7, 1, 1, 1, 1, 3, 5]
def baseStart_3925672 : Nat := 118140960795 + 3925672 * 2 ^ 59
def prefixEnd_3925672 : Nat := 4983230072969 + 3 ^ 40 * 3925672 * 2
def baseEnd_3925672 : Nat := 447945917310460005321371

theorem tailTrace_3925672 : CollatzResearch.WordTrace tailWord_3925672 prefixEnd_3925672 447945917310460005321371 := by
  unfold tailWord_3925672
  simp only [CollatzResearch.WordTrace]
  refine ⟨71590510316984135122673635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95454013755978846830231513 71590510316984135122673635)
  ·
    refine ⟨107385765475476202684010453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71590510316984135122673635 107385765475476202684010453)
    ·
      refine ⟨2516853878331473500406495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 107385765475476202684010453 2516853878331473500406495)
      ·
        refine ⟨3775280817497210250609743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2516853878331473500406495 3775280817497210250609743)
        ·
          refine ⟨5662921226245815375914615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3775280817497210250609743 5662921226245815375914615)
          ·
            refine ⟨8494381839368723063871923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5662921226245815375914615 8494381839368723063871923)
            ·
              refine ⟨12741572759053084595807885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8494381839368723063871923 12741572759053084595807885)
              ·
                refine ⟨4778089784644906723427957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12741572759053084595807885 4778089784644906723427957)
                ·
                  refine ⟨447945917310460005321371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4778089784644906723427957 447945917310460005321371)
                  ·
                    rfl

theorem cell22_3925672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 5].length) (baseStart_3925672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925672 prefixEnd_3925672 := by exact prefixLift 3925672
  have htrace : WordTrace (prefixWord ++ tailWord_3925672) baseStart_3925672 baseEnd_3925672 := by
    simpa [prefixWord, tailWord_3925672, baseEnd_3925672] using wordTrace_append hprefix tailTrace_3925672
  have hstable : (prefixWord ++ tailWord_3925672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925672).length < 2 ^ (prefixWord ++ tailWord_3925672).sum := by decide
  have hdescent : baseEnd_3925672 < baseStart_3925672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925743 : List Nat := [1, 1, 2, 1, 5, 1, 3, 2, 3, 3]
def baseStart_3925743 : Nat := 118140960795 + 3925743 * 2 ^ 59
def prefixEnd_3925743 : Nat := 4983230072969 + 3 ^ 40 * 3925743 * 2
def baseEnd_3925743 : Nat := 1343862056682359497438895

theorem tailTrace_3925743 : CollatzResearch.WordTrace tailWord_3925743 prefixEnd_3925743 1343862056682359497438895 := by
  unfold tailWord_3925743
  simp only [CollatzResearch.WordTrace]
  refine ⟨143183610216711049371181883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95455740144474032914121255 143183610216711049371181883)
  ·
    refine ⟨214775415325066574056772825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143183610216711049371181883 214775415325066574056772825)
    ·
      refine ⟨161081561493799930542579619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214775415325066574056772825 161081561493799930542579619)
      ·
        refine ⟨241622342240699895813869429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161081561493799930542579619 241622342240699895813869429)
        ·
          refine ⟨22652094585065615232550259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241622342240699895813869429 22652094585065615232550259)
          ·
            refine ⟨33978141877598422848825389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22652094585065615232550259 33978141877598422848825389)
            ·
              refine ⟨12741803204099408568309521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33978141877598422848825389 12741803204099408568309521)
              ·
                refine ⟨9556352403074556426232141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12741803204099408568309521 9556352403074556426232141)
                ·
                  refine ⟨3583632151152958659837053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9556352403074556426232141 3583632151152958659837053)
                  ·
                    refine ⟨1343862056682359497438895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3583632151152958659837053 1343862056682359497438895)
                    ·
                      rfl

theorem cell22_3925743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 3].length) (baseStart_3925743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925743 prefixEnd_3925743 := by exact prefixLift 3925743
  have htrace : WordTrace (prefixWord ++ tailWord_3925743) baseStart_3925743 baseEnd_3925743 := by
    simpa [prefixWord, tailWord_3925743, baseEnd_3925743] using wordTrace_append hprefix tailTrace_3925743
  have hstable : (prefixWord ++ tailWord_3925743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925743).length < 2 ^ (prefixWord ++ tailWord_3925743).sum := by decide
  have hdescent : baseEnd_3925743 < baseStart_3925743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925756 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 7]
def baseStart_3925756 : Nat := 118140960795 + 3925756 * 2 ^ 59
def prefixEnd_3925756 : Nat := 4983230072969 + 3 ^ 40 * 3925756 * 2
def baseEnd_3925756 : Nat := 447955502282677265621285

theorem tailTrace_3925756 : CollatzResearch.WordTrace tailWord_3925756 prefixEnd_3925756 447955502282677265621285 := by
  unfold tailWord_3925756
  simp only [CollatzResearch.WordTrace]
  refine ⟨71592042182831976295702561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95456056243775968394270081 71592042182831976295702561)
  ·
    refine ⟨53694031637123982221776921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71592042182831976295702561 53694031637123982221776921)
    ·
      refine ⟨40270523727842986666332691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53694031637123982221776921 40270523727842986666332691)
      ·
        refine ⟨60405785591764479999499037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40270523727842986666332691 60405785591764479999499037)
        ·
          refine ⟨22652169596911679999812139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60405785591764479999499037 22652169596911679999812139)
          ·
            refine ⟨33978254395367519999718209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22652169596911679999812139 33978254395367519999718209)
            ·
              refine ⟨25483690796525639999788657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33978254395367519999718209 25483690796525639999788657)
              ·
                refine ⟨19112768097394229999841493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25483690796525639999788657 19112768097394229999841493)
                ·
                  refine ⟨447955502282677265621285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19112768097394229999841493 447955502282677265621285)
                  ·
                    rfl

theorem cell22_3925756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_3925756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925756 prefixEnd_3925756 := by exact prefixLift 3925756
  have htrace : WordTrace (prefixWord ++ tailWord_3925756) baseStart_3925756 baseEnd_3925756 := by
    simpa [prefixWord, tailWord_3925756, baseEnd_3925756] using wordTrace_append hprefix tailTrace_3925756
  have hstable : (prefixWord ++ tailWord_3925756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925756).length < 2 ^ (prefixWord ++ tailWord_3925756).sum := by decide
  have hdescent : baseEnd_3925756 < baseStart_3925756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925771 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 2, 5]
def baseStart_3925771 : Nat := 118140960795 + 3925771 * 2 ^ 59
def prefixEnd_3925771 : Nat := 4983230072969 + 3 ^ 40 * 3925771 * 2
def baseEnd_3925771 : Nat := 1343871641654576757738809

theorem tailTrace_3925771 : CollatzResearch.WordTrace tailWord_3925771 prefixEnd_3925771 1343871641654576757738809 := by
  unfold tailWord_3925771
  simp only [CollatzResearch.WordTrace]
  refine ⟨143184631460609610153201167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95456420973739740102134111 143184631460609610153201167)
  ·
    refine ⟨214776947190914415229801751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143184631460609610153201167 214776947190914415229801751)
    ·
      refine ⟨322165420786371622844702627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214776947190914415229801751 322165420786371622844702627)
      ·
        refine ⟨483248131179557434267053941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322165420786371622844702627 483248131179557434267053941)
        ·
          refine ⟨45304512298083509462536307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 483248131179557434267053941 45304512298083509462536307)
          ·
            refine ⟨67956768447125264193804461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45304512298083509462536307 67956768447125264193804461)
            ·
              refine ⟨25483788167671974072676673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67956768447125264193804461 25483788167671974072676673)
              ·
                refine ⟨19112841125753980554507505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25483788167671974072676673 19112841125753980554507505)
                ·
                  refine ⟨14334630844315485415880629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19112841125753980554507505 14334630844315485415880629)
                  ·
                    refine ⟨1343871641654576757738809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14334630844315485415880629 1343871641654576757738809)
                    ·
                      rfl

theorem cell22_3925771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 5].length) (baseStart_3925771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925771 prefixEnd_3925771 := by exact prefixLift 3925771
  have htrace : WordTrace (prefixWord ++ tailWord_3925771) baseStart_3925771 baseEnd_3925771 := by
    simpa [prefixWord, tailWord_3925771, baseEnd_3925771] using wordTrace_append hprefix tailTrace_3925771
  have hstable : (prefixWord ++ tailWord_3925771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925771).length < 2 ^ (prefixWord ++ tailWord_3925771).sum := by decide
  have hdescent : baseEnd_3925771 < baseStart_3925771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925833 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 4, 3]
def baseStart_3925833 : Nat := 118140960795 + 3925833 * 2 ^ 59
def prefixEnd_3925833 : Nat := 4983230072969 + 3 ^ 40 * 3925833 * 2
def baseEnd_3925833 : Nat := 1343892865521629262688619

theorem tailTrace_3925833 : CollatzResearch.WordTrace tailWord_3925833 prefixEnd_3925833 1343892865521629262688619 := by
  unfold tailWord_3925833
  simp only [CollatzResearch.WordTrace]
  refine ⟨143186892786384994741958153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95457928524256663161305435 143186892786384994741958153)
  ·
    refine ⟨107390169589788746056468615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143186892786384994741958153 107390169589788746056468615)
    ·
      refine ⟨161085254384683119084702923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107390169589788746056468615 161085254384683119084702923)
      ·
        refine ⟨241627881577024678627054385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161085254384683119084702923 241627881577024678627054385)
        ·
          refine ⟨181220911182768508970290789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241627881577024678627054385 181220911182768508970290789)
          ·
            refine ⟨33978920846769095431929523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181220911182768508970290789 33978920846769095431929523)
            ·
              refine ⟨50968381270153643147894285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33978920846769095431929523 50968381270153643147894285)
              ·
                refine ⟨19113142976307616180460357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50968381270153643147894285 19113142976307616180460357)
                ·
                  refine ⟨3583714308057678033836317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19113142976307616180460357 3583714308057678033836317)
                  ·
                    refine ⟨1343892865521629262688619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3583714308057678033836317 1343892865521629262688619)
                    ·
                      rfl

theorem cell22_3925833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 3].length) (baseStart_3925833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925833 prefixEnd_3925833 := by exact prefixLift 3925833
  have htrace : WordTrace (prefixWord ++ tailWord_3925833) baseStart_3925833 baseEnd_3925833 := by
    simpa [prefixWord, tailWord_3925833, baseEnd_3925833] using wordTrace_append hprefix tailTrace_3925833
  have hstable : (prefixWord ++ tailWord_3925833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925833).length < 2 ^ (prefixWord ++ tailWord_3925833).sum := by decide
  have hdescent : baseEnd_3925833 < baseStart_3925833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925850 : List Nat := [3, 1, 1, 2, 1, 3, 3, 3, 2, 3]
def baseStart_3925850 : Nat := 118140960795 + 3925850 * 2 ^ 59
def prefixEnd_3925850 : Nat := 4983230072969 + 3 ^ 40 * 3925850 * 2
def baseEnd_3925850 : Nat := 1343898684969046885013567

theorem tailTrace_3925850 : CollatzResearch.WordTrace tailWord_3925850 prefixEnd_3925850 1343898684969046885013567 := by
  unfold tailWord_3925850
  simp only [CollatzResearch.WordTrace]
  refine ⟨35796878206830851661331751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95458341884882271096884669 35796878206830851661331751)
  ·
    refine ⟨53695317310246277491997627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35796878206830851661331751 53695317310246277491997627)
    ·
      refine ⟨80542975965369416237996441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53695317310246277491997627 80542975965369416237996441)
      ·
        refine ⟨60407231974027062178497331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80542975965369416237996441 60407231974027062178497331)
        ·
          refine ⟨90610847961040593267745997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60407231974027062178497331 90610847961040593267745997)
          ·
            refine ⟨33979067985390222475404749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90610847961040593267745997 33979067985390222475404749)
            ·
              refine ⟨12742150494521333428276781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33979067985390222475404749 12742150494521333428276781)
              ·
                refine ⟨4778306435445500035603793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12742150494521333428276781 4778306435445500035603793)
                ·
                  refine ⟨3583729826584125026702845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4778306435445500035603793 3583729826584125026702845)
                  ·
                    refine ⟨1343898684969046885013567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3583729826584125026702845 1343898684969046885013567)
                    ·
                      rfl

theorem cell22_3925850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_3925850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925850 prefixEnd_3925850 := by exact prefixLift 3925850
  have htrace : WordTrace (prefixWord ++ tailWord_3925850) baseStart_3925850 baseEnd_3925850 := by
    simpa [prefixWord, tailWord_3925850, baseEnd_3925850] using wordTrace_append hprefix tailTrace_3925850
  have hstable : (prefixWord ++ tailWord_3925850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925850).length < 2 ^ (prefixWord ++ tailWord_3925850).sum := by decide
  have hdescent : baseEnd_3925850 < baseStart_3925850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925886 : List Nat := [4, 2, 3, 1, 1, 3, 2, 2, 4]
def baseStart_3925886 : Nat := 118140960795 + 3925886 * 2 ^ 59
def prefixEnd_3925886 : Nat := 4983230072969 + 3 ^ 40 * 3925886 * 2
def baseEnd_3925886 : Nat := 447970336168251597037819

theorem tailTrace_3925886 : CollatzResearch.WordTrace tailWord_3925886 prefixEnd_3925886 447970336168251597037819 := by
  unfold tailWord_3925886
  simp only [CollatzResearch.WordTrace]
  refine ⟨17898603231899123099204689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95459217236795323195758341 17898603231899123099204689)
  ·
    refine ⟨13423952423924342324403517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17898603231899123099204689 13423952423924342324403517)
    ·
      refine ⟨5033982158971628371651319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13423952423924342324403517 5033982158971628371651319)
      ·
        refine ⟨7550973238457442557476979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5033982158971628371651319 7550973238457442557476979)
        ·
          refine ⟨11326459857686163836215469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7550973238457442557476979 11326459857686163836215469)
          ·
            refine ⟨4247422446632311438580801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11326459857686163836215469 4247422446632311438580801)
            ·
              refine ⟨3185566834974233578935601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4247422446632311438580801 3185566834974233578935601)
              ·
                refine ⟨2389175126230675184201701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3185566834974233578935601 2389175126230675184201701)
                ·
                  refine ⟨447970336168251597037819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2389175126230675184201701 447970336168251597037819)
                  ·
                    rfl

theorem cell22_3925886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_3925886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925886 prefixEnd_3925886 := by exact prefixLift 3925886
  have htrace : WordTrace (prefixWord ++ tailWord_3925886) baseStart_3925886 baseEnd_3925886 := by
    simpa [prefixWord, tailWord_3925886, baseEnd_3925886] using wordTrace_append hprefix tailTrace_3925886
  have hstable : (prefixWord ++ tailWord_3925886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925886).length < 2 ^ (prefixWord ++ tailWord_3925886).sum := by decide
  have hdescent : baseEnd_3925886 < baseStart_3925886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925972 : List Nat := [2, 4, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_3925972 : Nat := 118140960795 + 3925972 * 2 ^ 59
def prefixEnd_3925972 : Nat := 4983230072969 + 3 ^ 40 * 3925972 * 2
def baseEnd_3925972 : Nat := 1343940448062279233463193

theorem tailTrace_3925972 : CollatzResearch.WordTrace tailWord_3925972 prefixEnd_3925972 1343940448062279233463193 := by
  unfold tailWord_3925972
  simp only [CollatzResearch.WordTrace]
  refine ⟨71595981266440710740634085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95461308355254280987512113 71595981266440710740634085)
  ·
    refine ⟨13424246487457633263868891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71595981266440710740634085 13424246487457633263868891)
    ·
      refine ⟨20136369731186449895803337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13424246487457633263868891 20136369731186449895803337)
      ·
        refine ⟨15102277298389837421852503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20136369731186449895803337 15102277298389837421852503)
        ·
          refine ⟨22653415947584756132778755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15102277298389837421852503 22653415947584756132778755)
          ·
            refine ⟨33980123921377134199168133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22653415947584756132778755 33980123921377134199168133)
            ·
              refine ⟨6371273235258212662344025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33980123921377134199168133 6371273235258212662344025)
              ·
                refine ⟨4778454926443659496758019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6371273235258212662344025 4778454926443659496758019)
                ·
                  refine ⟨7167682389665489245137029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4778454926443659496758019 7167682389665489245137029)
                  ·
                    refine ⟨1343940448062279233463193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7167682389665489245137029 1343940448062279233463193)
                    ·
                      rfl

theorem cell22_3925972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_3925972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925972 prefixEnd_3925972 := by exact prefixLift 3925972
  have htrace : WordTrace (prefixWord ++ tailWord_3925972) baseStart_3925972 baseEnd_3925972 := by
    simpa [prefixWord, tailWord_3925972, baseEnd_3925972] using wordTrace_append hprefix tailTrace_3925972
  have hstable : (prefixWord ++ tailWord_3925972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925972).length < 2 ^ (prefixWord ++ tailWord_3925972).sum := by decide
  have hdescent : baseEnd_3925972 < baseStart_3925972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925980 : List Nat := [2, 2, 6, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3925980 : Nat := 118140960795 + 3925980 * 2 ^ 59
def prefixEnd_3925980 : Nat := 4983230072969 + 3 ^ 40 * 3925980 * 2
def baseEnd_3925980 : Nat := 1343943186625769879263169

theorem tailTrace_3925980 : CollatzResearch.WordTrace tailWord_3925980 prefixEnd_3925980 1343943186625769879263169 := by
  unfold tailWord_3925980
  simp only [CollatzResearch.WordTrace]
  refine ⟨71596127158426219423779697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95461502877901625898372929 71596127158426219423779697)
  ·
    refine ⟨53697095368819664567834773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71596127158426219423779697 53697095368819664567834773)
    ·
      refine ⟨2517051345413421776617255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53697095368819664567834773 2517051345413421776617255)
      ·
        refine ⟨3775577018120132664925883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2517051345413421776617255 3775577018120132664925883)
        ·
          refine ⟨5663365527180198997388825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3775577018120132664925883 5663365527180198997388825)
          ·
            refine ⟨4247524145385149248041619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5663365527180198997388825 4247524145385149248041619)
            ·
              refine ⟨6371286218077723872062429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4247524145385149248041619 6371286218077723872062429)
              ·
                refine ⟨2389232331779146452023411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6371286218077723872062429 2389232331779146452023411)
                ·
                  refine ⟨3583848497668719678035117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2389232331779146452023411 3583848497668719678035117)
                  ·
                    refine ⟨1343943186625769879263169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3583848497668719678035117 1343943186625769879263169)
                    ·
                      rfl

theorem cell22_3925980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3925980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925980 prefixEnd_3925980 := by exact prefixLift 3925980
  have htrace : WordTrace (prefixWord ++ tailWord_3925980) baseStart_3925980 baseEnd_3925980 := by
    simpa [prefixWord, tailWord_3925980, baseEnd_3925980] using wordTrace_append hprefix tailTrace_3925980
  have hstable : (prefixWord ++ tailWord_3925980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925980).length < 2 ^ (prefixWord ++ tailWord_3925980).sum := by decide
  have hdescent : baseEnd_3925980 < baseStart_3925980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925985 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 4, 3]
def baseStart_3925985 : Nat := 118140960795 + 3925985 * 2 ^ 59
def prefixEnd_3925985 : Nat := 4983230072969 + 3 ^ 40 * 3925985 * 2
def baseEnd_3925985 : Nat := 1343944898227951532888153

theorem tailTrace_3925985 : CollatzResearch.WordTrace tailWord_3925985 prefixEnd_3925985 1343944898227951532888153 := by
  unfold tailWord_3925985
  simp only [CollatzResearch.WordTrace]
  refine ⟨143192436681834324701491409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95461624454556216467660939 143192436681834324701491409)
  ·
    refine ⟨107394327511375743526118557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143192436681834324701491409 107394327511375743526118557)
    ·
      refine ⟨40272872816765903822294459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107394327511375743526118557 40272872816765903822294459)
      ·
        refine ⟨60409309225148855733441689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40272872816765903822294459 60409309225148855733441689)
        ·
          refine ⟨45306981918861641800081267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60409309225148855733441689 45306981918861641800081267)
          ·
            refine ⟨67960472878292462700121901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45306981918861641800081267 67960472878292462700121901)
            ·
              refine ⟨25485177329359673512545713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67960472878292462700121901 25485177329359673512545713)
              ·
                refine ⟨19113882997019755134409285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25485177329359673512545713 19113882997019755134409285)
                ·
                  refine ⟨3583853061941204087701741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19113882997019755134409285 3583853061941204087701741)
                  ·
                    refine ⟨1343944898227951532888153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3583853061941204087701741 1343944898227951532888153)
                    ·
                      rfl

theorem cell22_3925985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_3925985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925985 prefixEnd_3925985 := by exact prefixLift 3925985
  have htrace : WordTrace (prefixWord ++ tailWord_3925985) baseStart_3925985 baseEnd_3925985 := by
    simpa [prefixWord, tailWord_3925985, baseEnd_3925985] using wordTrace_append hprefix tailTrace_3925985
  have hstable : (prefixWord ++ tailWord_3925985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925985).length < 2 ^ (prefixWord ++ tailWord_3925985).sum := by decide
  have hdescent : baseEnd_3925985 < baseStart_3925985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925987 : List Nat := [1, 1, 1, 6, 1, 2, 3, 3, 4]
def baseStart_3925987 : Nat := 118140960795 + 3925987 * 2 ^ 59
def prefixEnd_3925987 : Nat := 4983230072969 + 3 ^ 40 * 3925987 * 2
def baseEnd_3925987 : Nat := 447981860956274731446049

theorem tailTrace_3925987 : CollatzResearch.WordTrace tailWord_3925987 prefixEnd_3925987 447981860956274731446049 := by
  unfold tailWord_3925987
  simp only [CollatzResearch.WordTrace]
  refine ⟨143192509627827079043064215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95461673085218052695376143 143192509627827079043064215)
  ·
    refine ⟨214788764441740618564596323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143192509627827079043064215 214788764441740618564596323)
    ·
      refine ⟨322183146662610927846894485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214788764441740618564596323 322183146662610927846894485)
      ·
        refine ⟨15102334999809887242823179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 322183146662610927846894485 15102334999809887242823179)
        ·
          refine ⟨22653502499714830864234769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15102334999809887242823179 22653502499714830864234769)
          ·
            refine ⟨16990126874786123148176077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22653502499714830864234769 16990126874786123148176077)
            ·
              refine ⟨6371297578044796180566029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16990126874786123148176077 6371297578044796180566029)
              ·
                refine ⟨2389236591766798567712261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6371297578044796180566029 2389236591766798567712261)
                ·
                  refine ⟨447981860956274731446049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2389236591766798567712261 447981860956274731446049)
                  ·
                    rfl

theorem cell22_3925987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 4].length) (baseStart_3925987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3925987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3925987 prefixEnd_3925987 := by exact prefixLift 3925987
  have htrace : WordTrace (prefixWord ++ tailWord_3925987) baseStart_3925987 baseEnd_3925987 := by
    simpa [prefixWord, tailWord_3925987, baseEnd_3925987] using wordTrace_append hprefix tailTrace_3925987
  have hstable : (prefixWord ++ tailWord_3925987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925987).length < 2 ^ (prefixWord ++ tailWord_3925987).sum := by decide
  have hdescent : baseEnd_3925987 < baseStart_3925987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926043 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 7]
def baseStart_3926043 : Nat := 118140960795 + 3926043 * 2 ^ 59
def prefixEnd_3926043 : Nat := 4983230072969 + 3 ^ 40 * 3926043 * 2
def baseEnd_3926043 : Nat := 447988250937752904979325

theorem tailTrace_3926043 : CollatzResearch.WordTrace tailWord_3926043 prefixEnd_3926043 447988250937752904979325 := by
  unfold tailWord_3926043
  simp only [CollatzResearch.WordTrace]
  refine ⟨143194552115624200607102783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95463034743749467071401855 143194552115624200607102783)
  ·
    refine ⟨214791828173436300910654175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143194552115624200607102783 214791828173436300910654175)
    ·
      refine ⟨322187742260154451365981263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214791828173436300910654175 322187742260154451365981263)
      ·
        refine ⟨483281613390231677048971895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322187742260154451365981263 483281613390231677048971895)
        ·
          refine ⟨724922420085347515573457843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483281613390231677048971895 724922420085347515573457843)
          ·
            refine ⟨1087383630128021273360186765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724922420085347515573457843 1087383630128021273360186765)
            ·
              refine ⟨407768861298007977510070037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1087383630128021273360186765 407768861298007977510070037)
              ·
                refine ⟨19114165373344123945784533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 407768861298007977510070037 19114165373344123945784533)
                ·
                  refine ⟨447988250937752904979325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19114165373344123945784533 447988250937752904979325)
                  ·
                    rfl

theorem cell22_3926043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 7].length) (baseStart_3926043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926043 prefixEnd_3926043 := by exact prefixLift 3926043
  have htrace : WordTrace (prefixWord ++ tailWord_3926043) baseStart_3926043 baseEnd_3926043 := by
    simpa [prefixWord, tailWord_3926043, baseEnd_3926043] using wordTrace_append hprefix tailTrace_3926043
  have hstable : (prefixWord ++ tailWord_3926043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926043).length < 2 ^ (prefixWord ++ tailWord_3926043).sum := by decide
  have hdescent : baseEnd_3926043 < baseStart_3926043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926064 : List Nat := [2, 1, 1, 1, 2, 6, 1, 4, 1, 3]
def baseStart_3926064 : Nat := 118140960795 + 3926064 * 2 ^ 59
def prefixEnd_3926064 : Nat := 4983230072969 + 3 ^ 40 * 3926064 * 2
def baseEnd_3926064 : Nat := 1343971941542421660162911

theorem tailTrace_3926064 : CollatzResearch.WordTrace tailWord_3926064 prefixEnd_3926064 1343971941542421660162911 := by
  unfold tailWord_3926064
  simp only [CollatzResearch.WordTrace]
  refine ⟨71597659024274060596808623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95463545365698747462411497 71597659024274060596808623)
  ·
    refine ⟨107396488536411090895212935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71597659024274060596808623 107396488536411090895212935)
    ·
      refine ⟨161094732804616636342819403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107396488536411090895212935 161094732804616636342819403)
      ·
        refine ⟨241642099206924954514229105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161094732804616636342819403 241642099206924954514229105)
        ·
          refine ⟨181231574405193715885671829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241642099206924954514229105 181231574405193715885671829)
          ·
            refine ⟨8495230050243455432140867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 181231574405193715885671829 8495230050243455432140867)
            ·
              refine ⟨12742845075365183148211301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8495230050243455432140867 12742845075365183148211301)
              ·
                refine ⟨2389283451630971840289619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12742845075365183148211301 2389283451630971840289619)
                ·
                  refine ⟨3583925177446457760434429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2389283451630971840289619 3583925177446457760434429)
                  ·
                    refine ⟨1343971941542421660162911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3583925177446457760434429 1343971941542421660162911)
                    ·
                      rfl

theorem cell22_3926064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 1, 3].length) (baseStart_3926064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926064 prefixEnd_3926064 := by exact prefixLift 3926064
  have htrace : WordTrace (prefixWord ++ tailWord_3926064) baseStart_3926064 baseEnd_3926064 := by
    simpa [prefixWord, tailWord_3926064, baseEnd_3926064] using wordTrace_append hprefix tailTrace_3926064
  have hstable : (prefixWord ++ tailWord_3926064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926064).length < 2 ^ (prefixWord ++ tailWord_3926064).sum := by decide
  have hdescent : baseEnd_3926064 < baseStart_3926064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926135 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 1, 6]
def baseStart_3926135 : Nat := 118140960795 + 3926135 * 2 ^ 59
def prefixEnd_3926135 : Nat := 4983230072969 + 3 ^ 40 * 3926135 * 2
def baseEnd_3926135 : Nat := 1343996246293401141637693

theorem tailTrace_3926135 : CollatzResearch.WordTrace tailWord_3926135 prefixEnd_3926135 1343996246293401141637693 := by
  unfold tailWord_3926135
  simp only [CollatzResearch.WordTrace]
  refine ⟨143197907631290900319451859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95465271754193933546301239 143197907631290900319451859)
  ·
    refine ⟨214796861446936350479177789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143197907631290900319451859 214796861446936350479177789)
    ·
      refine ⟨80548823042601131429691671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214796861446936350479177789 80548823042601131429691671)
      ·
        refine ⟨120823234563901697144537507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80548823042601131429691671 120823234563901697144537507)
        ·
          refine ⟨181234851845852545716806261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120823234563901697144537507 181234851845852545716806261)
          ·
            refine ⟨16990767360548676160950587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181234851845852545716806261 16990767360548676160950587)
            ·
              refine ⟨25486151040823014241425881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16990767360548676160950587 25486151040823014241425881)
              ·
                refine ⟨19114613280617260681069411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25486151040823014241425881 19114613280617260681069411)
                ·
                  refine ⟨28671919920925891021604117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19114613280617260681069411 28671919920925891021604117)
                  ·
                    refine ⟨1343996246293401141637693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28671919920925891021604117 1343996246293401141637693)
                    ·
                      rfl

theorem cell22_3926135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_3926135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926135 prefixEnd_3926135 := by exact prefixLift 3926135
  have htrace : WordTrace (prefixWord ++ tailWord_3926135) baseStart_3926135 baseEnd_3926135 := by
    simpa [prefixWord, tailWord_3926135, baseEnd_3926135] using wordTrace_append hprefix tailTrace_3926135
  have hstable : (prefixWord ++ tailWord_3926135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926135).length < 2 ^ (prefixWord ++ tailWord_3926135).sum := by decide
  have hdescent : baseEnd_3926135 < baseStart_3926135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926137 : List Nat := [1, 2, 1, 3, 4, 1, 3, 1, 1, 5]
def baseStart_3926137 : Nat := 118140960795 + 3926137 * 2 ^ 59
def prefixEnd_3926137 : Nat := 4983230072969 + 3 ^ 40 * 3926137 * 2
def baseEnd_3926137 : Nat := 1343996930934273803087687

theorem tailTrace_3926137 : CollatzResearch.WordTrace tailWord_3926137 prefixEnd_3926137 1343996930934273803087687 := by
  unfold tailWord_3926137
  simp only [CollatzResearch.WordTrace]
  refine ⟨143197980577283654661024665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95465320384855769774016443 143197980577283654661024665)
  ·
    refine ⟨107398485432962740995768499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143197980577283654661024665 107398485432962740995768499)
    ·
      refine ⟨161097728149444111493652749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107398485432962740995768499 161097728149444111493652749)
      ·
        refine ⟨60411648056041541810119781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161097728149444111493652749 60411648056041541810119781)
        ·
          refine ⟨11327184010507789089397459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60411648056041541810119781 11327184010507789089397459)
          ·
            refine ⟨16990776015761683634096189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11327184010507789089397459 16990776015761683634096189)
            ·
              refine ⟨6371541005910631362786071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16990776015761683634096189 6371541005910631362786071)
              ·
                refine ⟨9557311508865947044179107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6371541005910631362786071 9557311508865947044179107)
                ·
                  refine ⟨14335967263298920566268661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9557311508865947044179107 14335967263298920566268661)
                  ·
                    refine ⟨1343996930934273803087687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14335967263298920566268661 1343996930934273803087687)
                    ·
                      rfl

theorem cell22_3926137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 5].length) (baseStart_3926137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926137 prefixEnd_3926137 := by exact prefixLift 3926137
  have htrace : WordTrace (prefixWord ++ tailWord_3926137) baseStart_3926137 baseEnd_3926137 := by
    simpa [prefixWord, tailWord_3926137, baseEnd_3926137] using wordTrace_append hprefix tailTrace_3926137
  have hstable : (prefixWord ++ tailWord_3926137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926137).length < 2 ^ (prefixWord ++ tailWord_3926137).sum := by decide
  have hdescent : baseEnd_3926137 < baseStart_3926137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926152 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 1, 6]
def baseStart_3926152 : Nat := 118140960795 + 3926152 * 2 ^ 59
def prefixEnd_3926152 : Nat := 4983230072969 + 3 ^ 40 * 3926152 * 2
def baseEnd_3926152 : Nat := 1344002065740818763962641

theorem tailTrace_3926152 : CollatzResearch.WordTrace tailWord_3926152 prefixEnd_3926152 1344002065740818763962641 := by
  unfold tailWord_3926152
  simp only [CollatzResearch.WordTrace]
  refine ⟨71599263836114656111410355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95465685114819541481880473 71599263836114656111410355)
  ·
    refine ⟨107398895754171984167115533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71599263836114656111410355 107398895754171984167115533)
    ·
      refine ⟨40274585907814494062668325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107398895754171984167115533 40274585907814494062668325)
      ·
        refine ⟨7551484857715217636750311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40274585907814494062668325 7551484857715217636750311)
        ·
          refine ⟨11327227286572826455125467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7551484857715217636750311 11327227286572826455125467)
          ·
            refine ⟨16990840929859239682688201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11327227286572826455125467 16990840929859239682688201)
            ·
              refine ⟨12743130697394429762016151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16990840929859239682688201 12743130697394429762016151)
              ·
                refine ⟨19114696046091644643024227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12743130697394429762016151 19114696046091644643024227)
                ·
                  refine ⟨28672044069137466964536341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19114696046091644643024227 28672044069137466964536341)
                  ·
                    refine ⟨1344002065740818763962641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28672044069137466964536341 1344002065740818763962641)
                    ·
                      rfl

theorem cell22_3926152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_3926152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926152 prefixEnd_3926152 := by exact prefixLift 3926152
  have htrace : WordTrace (prefixWord ++ tailWord_3926152) baseStart_3926152 baseEnd_3926152 := by
    simpa [prefixWord, tailWord_3926152, baseEnd_3926152] using wordTrace_append hprefix tailTrace_3926152
  have hstable : (prefixWord ++ tailWord_3926152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926152).length < 2 ^ (prefixWord ++ tailWord_3926152).sum := by decide
  have hdescent : baseEnd_3926152 < baseStart_3926152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926167 : List Nat := [1, 1, 3, 3, 4, 2, 8]
def baseStart_3926167 : Nat := 118140960795 + 3926167 * 2 ^ 59
def prefixEnd_3926167 : Nat := 4983230072969 + 3 ^ 40 * 3926167 * 2
def baseEnd_3926167 : Nat := 49778044464717174993985

theorem tailTrace_3926167 : CollatzResearch.WordTrace tailWord_3926167 prefixEnd_3926167 49778044464717174993985 := by
  unfold tailWord_3926167
  simp only [CollatzResearch.WordTrace]
  refine ⟨143199074767174969784616755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95466049844783313189744503 143199074767174969784616755)
  ·
    refine ⟨214798612150762454676925133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143199074767174969784616755 214798612150762454676925133)
    ·
      refine ⟨80549479556535920503846925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214798612150762454676925133 80549479556535920503846925)
      ·
        refine ⟨30206054833700970188942597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80549479556535920503846925 30206054833700970188942597)
        ·
          refine ⟨5663635281318931910426737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30206054833700970188942597 5663635281318931910426737)
          ·
            refine ⟨4247726460989198932820053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5663635281318931910426737 4247726460989198932820053)
            ·
              refine ⟨49778044464717174993985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4247726460989198932820053 49778044464717174993985)
              ·
                rfl

theorem cell22_3926167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 8].length) (baseStart_3926167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926167 prefixEnd_3926167 := by exact prefixLift 3926167
  have htrace : WordTrace (prefixWord ++ tailWord_3926167) baseStart_3926167 baseEnd_3926167 := by
    simpa [prefixWord, tailWord_3926167, baseEnd_3926167] using wordTrace_append hprefix tailTrace_3926167
  have hstable : (prefixWord ++ tailWord_3926167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926167).length < 2 ^ (prefixWord ++ tailWord_3926167).sum := by decide
  have hdescent : baseEnd_3926167 < baseStart_3926167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926272 : List Nat := [2, 1, 1, 2, 1, 1, 6, 2, 1, 5]
def baseStart_3926272 : Nat := 118140960795 + 3926272 * 2 ^ 59
def prefixEnd_3926272 : Nat := 4983230072969 + 3 ^ 40 * 3926272 * 2
def baseEnd_3926272 : Nat := 1344043144193178450962273

theorem tailTrace_3926272 : CollatzResearch.WordTrace tailWord_3926272 prefixEnd_3926272 1344043144193178450962273 := by
  unfold tailWord_3926272
  simp only [CollatzResearch.WordTrace]
  refine ⟨71601452215897286358594535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95468602954529715144792713 71601452215897286358594535)
  ·
    refine ⟨107402178323845929537891803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71601452215897286358594535 107402178323845929537891803)
    ·
      refine ⟨161103267485768894306837705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107402178323845929537891803 161103267485768894306837705)
      ·
        refine ⟨120827450614326670730128279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161103267485768894306837705 120827450614326670730128279)
        ·
          refine ⟨181241175921490006095192419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120827450614326670730128279 181241175921490006095192419)
          ·
            refine ⟨271861763882235009142788629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181241175921490006095192419 271861763882235009142788629)
            ·
              refine ⟨12743520181979766053568217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 271861763882235009142788629 12743520181979766053568217)
              ·
                refine ⟨9557640136484824540176163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12743520181979766053568217 9557640136484824540176163)
                ·
                  refine ⟨14336460204727236810264245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9557640136484824540176163 14336460204727236810264245)
                  ·
                    refine ⟨1344043144193178450962273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14336460204727236810264245 1344043144193178450962273)
                    ·
                      rfl

theorem cell22_3926272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_3926272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926272 prefixEnd_3926272 := by exact prefixLift 3926272
  have htrace : WordTrace (prefixWord ++ tailWord_3926272) baseStart_3926272 baseEnd_3926272 := by
    simpa [prefixWord, tailWord_3926272, baseEnd_3926272] using wordTrace_append hprefix tailTrace_3926272
  have hstable : (prefixWord ++ tailWord_3926272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926272).length < 2 ^ (prefixWord ++ tailWord_3926272).sum := by decide
  have hdescent : baseEnd_3926272 < baseStart_3926272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926276 : List Nat := [2, 3, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_3926276 : Nat := 118140960795 + 3926276 * 2 ^ 59
def prefixEnd_3926276 : Nat := 4983230072969 + 3 ^ 40 * 3926276 * 2
def baseEnd_3926276 : Nat := 1344044513474923773862261

theorem tailTrace_3926276 : CollatzResearch.WordTrace tailWord_3926276 prefixEnd_3926276 1344044513474923773862261 := by
  unfold tailWord_3926276
  simp only [CollatzResearch.WordTrace]
  refine ⟨71601525161890040700167341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95468700215853387600223121 71601525161890040700167341)
  ·
    refine ⟨26850571935708765262562753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71601525161890040700167341 26850571935708765262562753)
    ·
      refine ⟨20137928951781573946922065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26850571935708765262562753 20137928951781573946922065)
      ·
        refine ⟨15103446713836180460191549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20137928951781573946922065 15103446713836180460191549)
        ·
          refine ⟨5663792517688567672571831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15103446713836180460191549 5663792517688567672571831)
          ·
            refine ⟨8495688776532851508857747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5663792517688567672571831 8495688776532851508857747)
            ·
              refine ⟨12743533164799277263286621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8495688776532851508857747 12743533164799277263286621)
              ·
                refine ⟨4778824936799728973732483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12743533164799277263286621 4778824936799728973732483)
                ·
                  refine ⟨7168237405199593460598725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4778824936799728973732483 7168237405199593460598725)
                  ·
                    refine ⟨1344044513474923773862261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7168237405199593460598725 1344044513474923773862261)
                    ·
                      rfl

theorem cell22_3926276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_3926276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926276 prefixEnd_3926276 := by exact prefixLift 3926276
  have htrace : WordTrace (prefixWord ++ tailWord_3926276) baseStart_3926276 baseEnd_3926276 := by
    simpa [prefixWord, tailWord_3926276, baseEnd_3926276] using wordTrace_append hprefix tailTrace_3926276
  have hstable : (prefixWord ++ tailWord_3926276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926276).length < 2 ^ (prefixWord ++ tailWord_3926276).sum := by decide
  have hdescent : baseEnd_3926276 < baseStart_3926276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926287 : List Nat := [1, 1, 2, 1, 1, 1, 3, 6, 2, 4]
def baseStart_3926287 : Nat := 118140960795 + 3926287 * 2 ^ 59
def prefixEnd_3926287 : Nat := 4983230072969 + 3 ^ 40 * 3926287 * 2
def baseEnd_3926287 : Nat := 1344048278999723411837227

theorem tailTrace_3926287 : CollatzResearch.WordTrace tailWord_3926287 prefixEnd_3926287 1344048278999723411837227 := by
  unfold tailWord_3926287
  simp only [CollatzResearch.WordTrace]
  refine ⟨143203451526740230278985115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95468967684493486852656743 143203451526740230278985115)
  ·
    refine ⟨214805177290110345418477673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143203451526740230278985115 214805177290110345418477673)
    ·
      refine ⟨161103882967582759063858255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214805177290110345418477673 161103882967582759063858255)
      ·
        refine ⟨241655824451374138595787383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161103882967582759063858255 241655824451374138595787383)
        ·
          refine ⟨362483736677061207893681075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241655824451374138595787383 362483736677061207893681075)
          ·
            refine ⟨543725605015591811840521613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362483736677061207893681075 543725605015591811840521613)
            ·
              refine ⟨203897101880846929440195605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 543725605015591811840521613 203897101880846929440195605)
              ·
                refine ⟨9557676650664699817509169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 203897101880846929440195605 9557676650664699817509169)
                ·
                  refine ⟨7168257487998524863131877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9557676650664699817509169 7168257487998524863131877)
                  ·
                    refine ⟨1344048278999723411837227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7168257487998524863131877 1344048278999723411837227)
                    ·
                      rfl

theorem cell22_3926287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_3926287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926287 prefixEnd_3926287 := by exact prefixLift 3926287
  have htrace : WordTrace (prefixWord ++ tailWord_3926287) baseStart_3926287 baseEnd_3926287 := by
    simpa [prefixWord, tailWord_3926287, baseEnd_3926287] using wordTrace_append hprefix tailTrace_3926287
  have hstable : (prefixWord ++ tailWord_3926287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926287).length < 2 ^ (prefixWord ++ tailWord_3926287).sum := by decide
  have hdescent : baseEnd_3926287 < baseStart_3926287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926289 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 4, 3]
def baseStart_3926289 : Nat := 118140960795 + 3926289 * 2 ^ 59
def prefixEnd_3926289 : Nat := 4983230072969 + 3 ^ 40 * 3926289 * 2
def baseEnd_3926289 : Nat := 1344048963640596073287221

theorem tailTrace_3926289 : CollatzResearch.WordTrace tailWord_3926289 prefixEnd_3926289 1344048963640596073287221 := by
  unfold tailWord_3926289
  simp only [CollatzResearch.WordTrace]
  refine ⟨143203524472732984620557921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95469016315155323080371947 143203524472732984620557921)
  ·
    refine ⟨107402643354549738465418441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143203524472732984620557921 107402643354549738465418441)
    ·
      refine ⟨80551982515912303849063831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107402643354549738465418441 80551982515912303849063831)
      ·
        refine ⟨120827973773868455773595747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80551982515912303849063831 120827973773868455773595747)
        ·
          refine ⟨181241960660802683660393621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120827973773868455773595747 181241960660802683660393621)
          ·
            refine ⟨8495716905975125796580951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 181241960660802683660393621 8495716905975125796580951)
            ·
              refine ⟨12743575358962688694871427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8495716905975125796580951 12743575358962688694871427)
              ·
                refine ⟨19115363038444033042307141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12743575358962688694871427 19115363038444033042307141)
                ·
                  refine ⟨3584130569708256195432589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19115363038444033042307141 3584130569708256195432589)
                  ·
                    refine ⟨1344048963640596073287221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3584130569708256195432589 1344048963640596073287221)
                    ·
                      rfl

theorem cell22_3926289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_3926289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926289 prefixEnd_3926289 := by exact prefixLift 3926289
  have htrace : WordTrace (prefixWord ++ tailWord_3926289) baseStart_3926289 baseEnd_3926289 := by
    simpa [prefixWord, tailWord_3926289, baseEnd_3926289] using wordTrace_append hprefix tailTrace_3926289
  have hstable : (prefixWord ++ tailWord_3926289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926289).length < 2 ^ (prefixWord ++ tailWord_3926289).sum := by decide
  have hdescent : baseEnd_3926289 < baseStart_3926289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926306 : List Nat := [3, 3, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_3926306 : Nat := 118140960795 + 3926306 * 2 ^ 59
def prefixEnd_3926306 : Nat := 4983230072969 + 3 ^ 40 * 3926306 * 2
def baseEnd_3926306 : Nat := 1344054783088013695612169

theorem tailTrace_3926306 : CollatzResearch.WordTrace tailWord_3926306 prefixEnd_3926306 1344054783088013695612169 := by
  unfold tailWord_3926306
  simp only [CollatzResearch.WordTrace]
  refine ⟨35801036128417849130981693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95469429675780931015951181 35801036128417849130981693)
  ·
    refine ⟨13425388548156693424118135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35801036128417849130981693 13425388548156693424118135)
    ·
      refine ⟨20138082822235040136177203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13425388548156693424118135 20138082822235040136177203)
      ·
        refine ⟨30207124233352560204265805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20138082822235040136177203 30207124233352560204265805)
        ·
          refine ⟨11327671587507210076599677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30207124233352560204265805 11327671587507210076599677)
          ·
            refine ⟨4247876845315203778724879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11327671587507210076599677 4247876845315203778724879)
            ·
              refine ⟨6371815267972805668087319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4247876845315203778724879 6371815267972805668087319)
              ·
                refine ⟨9557722901959208502130979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6371815267972805668087319 9557722901959208502130979)
                ·
                  refine ⟨14336584352938812753196469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9557722901959208502130979 14336584352938812753196469)
                  ·
                    refine ⟨1344054783088013695612169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14336584352938812753196469 1344054783088013695612169)
                    ·
                      rfl

theorem cell22_3926306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_3926306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926306 prefixEnd_3926306 := by exact prefixLift 3926306
  have htrace : WordTrace (prefixWord ++ tailWord_3926306) baseStart_3926306 baseEnd_3926306 := by
    simpa [prefixWord, tailWord_3926306, baseEnd_3926306] using wordTrace_append hprefix tailTrace_3926306
  have hstable : (prefixWord ++ tailWord_3926306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926306).length < 2 ^ (prefixWord ++ tailWord_3926306).sum := by decide
  have hdescent : baseEnd_3926306 < baseStart_3926306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926362 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 1, 7]
def baseStart_3926362 : Nat := 118140960795 + 3926362 * 2 ^ 59
def prefixEnd_3926362 : Nat := 4983230072969 + 3 ^ 40 * 3926362 * 2
def baseEnd_3926362 : Nat := 1344073953032448216211997

theorem tailTrace_3926362 : CollatzResearch.WordTrace tailWord_3926362 prefixEnd_3926362 1344073953032448216211997 := by
  unfold tailWord_3926362
  simp only [CollatzResearch.WordTrace]
  refine ⟨35801546750367129521991335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95470791334312345391976893 35801546750367129521991335)
  ·
    refine ⟨53702320125550694282987003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35801546750367129521991335 53702320125550694282987003)
    ·
      refine ⟨80553480188326041424480505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53702320125550694282987003 80553480188326041424480505)
      ·
        refine ⟨60415110141244531068360379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80553480188326041424480505 60415110141244531068360379)
        ·
          refine ⟨90622665211866796602540569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60415110141244531068360379 90622665211866796602540569)
          ·
            refine ⟨67966998908900097451905427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90622665211866796602540569 67966998908900097451905427)
            ·
              refine ⟨101950498363350146177858141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67966998908900097451905427 101950498363350146177858141)
              ·
                refine ⟨38231436886256304816696803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101950498363350146177858141 38231436886256304816696803)
                ·
                  refine ⟨57347155329384457225045205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38231436886256304816696803 57347155329384457225045205)
                  ·
                    refine ⟨1344073953032448216211997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57347155329384457225045205 1344073953032448216211997)
                    ·
                      rfl

theorem cell22_3926362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_3926362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926362 prefixEnd_3926362 := by exact prefixLift 3926362
  have htrace : WordTrace (prefixWord ++ tailWord_3926362) baseStart_3926362 baseEnd_3926362 := by
    simpa [prefixWord, tailWord_3926362, baseEnd_3926362] using wordTrace_append hprefix tailTrace_3926362
  have hstable : (prefixWord ++ tailWord_3926362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926362).length < 2 ^ (prefixWord ++ tailWord_3926362).sum := by decide
  have hdescent : baseEnd_3926362 < baseStart_3926362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926402 : List Nat := [3, 4, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_3926402 : Nat := 118140960795 + 3926402 * 2 ^ 59
def prefixEnd_3926402 : Nat := 4983230072969 + 3 ^ 40 * 3926402 * 2
def baseEnd_3926402 : Nat := 1344087645849901445211875

theorem tailTrace_3926402 : CollatzResearch.WordTrace tailWord_3926402 prefixEnd_3926402 1344087645849901445211875 := by
  unfold tailWord_3926402
  simp only [CollatzResearch.WordTrace]
  refine ⟨35801911480330901229855365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95471763947549069946280973 35801911480330901229855365)
  ·
    refine ⟨6712858402562043980597881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35801911480330901229855365 6712858402562043980597881)
    ·
      refine ⟨5034643801921532985448411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6712858402562043980597881 5034643801921532985448411)
      ·
        refine ⟨7551965702882299478172617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5034643801921532985448411 7551965702882299478172617)
        ·
          refine ⟨5663974277161724608629463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7551965702882299478172617 5663974277161724608629463)
          ·
            refine ⟨8495961415742586912944195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5663974277161724608629463 8495961415742586912944195)
            ·
              refine ⟨12743942123613880369416293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8495961415742586912944195 12743942123613880369416293)
              ·
                refine ⟨2389489148177602569265555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12743942123613880369416293 2389489148177602569265555)
                ·
                  refine ⟨3584233722266403853898333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2389489148177602569265555 3584233722266403853898333)
                  ·
                    refine ⟨1344087645849901445211875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3584233722266403853898333 1344087645849901445211875)
                    ·
                      rfl

theorem cell22_3926402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_3926402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926402 prefixEnd_3926402 := by exact prefixLift 3926402
  have htrace : WordTrace (prefixWord ++ tailWord_3926402) baseStart_3926402 baseEnd_3926402 := by
    simpa [prefixWord, tailWord_3926402, baseEnd_3926402] using wordTrace_append hprefix tailTrace_3926402
  have hstable : (prefixWord ++ tailWord_3926402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926402).length < 2 ^ (prefixWord ++ tailWord_3926402).sum := by decide
  have hdescent : baseEnd_3926402 < baseStart_3926402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926486 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_3926486 : Nat := 118140960795 + 3926486 * 2 ^ 59
def prefixEnd_3926486 : Nat := 4983230072969 + 3 ^ 40 * 3926486 * 2
def baseEnd_3926486 : Nat := 1344116400766553226111617

theorem tailTrace_3926486 : CollatzResearch.WordTrace tailWord_3926486 prefixEnd_3926486 1344116400766553226111617 := by
  unfold tailWord_3926486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8950669353313705454092457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95473806435346191510319541 8950669353313705454092457)
  ·
    refine ⟨6713002014985279090569343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8950669353313705454092457 6713002014985279090569343)
    ·
      refine ⟨10069503022477918635854015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6713002014985279090569343 10069503022477918635854015)
      ·
        refine ⟨15104254533716877953781023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10069503022477918635854015 15104254533716877953781023)
        ·
          refine ⟨22656381800575316930671535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15104254533716877953781023 22656381800575316930671535)
          ·
            refine ⟨33984572700862975396007303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22656381800575316930671535 33984572700862975396007303)
            ·
              refine ⟨50976859051294463094010955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33984572700862975396007303 50976859051294463094010955)
              ·
                refine ⟨76465288576941694641016433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50976859051294463094010955 76465288576941694641016433)
                ·
                  refine ⟨57348966432706270980762325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76465288576941694641016433 57348966432706270980762325)
                  ·
                    refine ⟨1344116400766553226111617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57348966432706270980762325 1344116400766553226111617)
                    ·
                      rfl

theorem cell22_3926486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_3926486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926486 prefixEnd_3926486 := by exact prefixLift 3926486
  have htrace : WordTrace (prefixWord ++ tailWord_3926486) baseStart_3926486 baseEnd_3926486 := by
    simpa [prefixWord, tailWord_3926486, baseEnd_3926486] using wordTrace_append hprefix tailTrace_3926486
  have hstable : (prefixWord ++ tailWord_3926486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926486).length < 2 ^ (prefixWord ++ tailWord_3926486).sum := by decide
  have hdescent : baseEnd_3926486 < baseStart_3926486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926520 : List Nat := [2, 1, 2, 1, 1, 4, 5, 2, 1, 3]
def baseStart_3926520 : Nat := 118140960795 + 3926520 * 2 ^ 59
def prefixEnd_3926520 : Nat := 4983230072969 + 3 ^ 40 * 3926520 * 2
def baseEnd_3926520 : Nat := 1344128039661388470761513

theorem tailTrace_3926520 : CollatzResearch.WordTrace tailWord_3926520 prefixEnd_3926520 1344128039661388470761513 := by
  unfold tailWord_3926520
  simp only [CollatzResearch.WordTrace]
  refine ⟨71605974867448055536108507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95474633156597407381478009 71605974867448055536108507)
  ·
    refine ⟨107408962301172083304162761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71605974867448055536108507 107408962301172083304162761)
    ·
      refine ⟨80556721725879062478122071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107408962301172083304162761 80556721725879062478122071)
      ·
        refine ⟨120835082588818593717183107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80556721725879062478122071 120835082588818593717183107)
        ·
          refine ⟨181252623883227890575774661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120835082588818593717183107 181252623883227890575774661)
          ·
            refine ⟨33984866978105229482957749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181252623883227890575774661 33984866978105229482957749)
            ·
              refine ⟨3186081279197365264027289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33984866978105229482957749 3186081279197365264027289)
              ·
                refine ⟨2389560959398023948020467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3186081279197365264027289 2389560959398023948020467)
                ·
                  refine ⟨3584341439097035922030701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2389560959398023948020467 3584341439097035922030701)
                  ·
                    refine ⟨1344128039661388470761513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3584341439097035922030701 1344128039661388470761513)
                    ·
                      rfl

theorem cell22_3926520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 1, 3].length) (baseStart_3926520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926520 prefixEnd_3926520 := by exact prefixLift 3926520
  have htrace : WordTrace (prefixWord ++ tailWord_3926520) baseStart_3926520 baseEnd_3926520 := by
    simpa [prefixWord, tailWord_3926520, baseEnd_3926520] using wordTrace_append hprefix tailTrace_3926520
  have hstable : (prefixWord ++ tailWord_3926520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926520).length < 2 ^ (prefixWord ++ tailWord_3926520).sum := by decide
  have hdescent : baseEnd_3926520 < baseStart_3926520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926576 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 4, 3]
def baseStart_3926576 : Nat := 118140960795 + 3926576 * 2 ^ 59
def prefixEnd_3926576 : Nat := 4983230072969 + 3 ^ 40 * 3926576 * 2
def baseEnd_3926576 : Nat := 1344147209605822991361341

theorem tailTrace_3926576 : CollatzResearch.WordTrace tailWord_3926576 prefixEnd_3926576 1344147209605822991361341 := by
  unfold tailWord_3926576
  simp only [CollatzResearch.WordTrace]
  refine ⟨71606996111346616318127791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95475994815128821757503721 71606996111346616318127791)
  ·
    refine ⟨107410494167019924477191687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71606996111346616318127791 107410494167019924477191687)
    ·
      refine ⟨161115741250529886715787531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107410494167019924477191687 161115741250529886715787531)
      ·
        refine ⟨241673611875794830073681297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161115741250529886715787531 241673611875794830073681297)
        ·
          refine ⟨181255208906846122555260973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241673611875794830073681297 181255208906846122555260973)
          ·
            refine ⟨67970703340067295958222865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181255208906846122555260973 67970703340067295958222865)
            ·
              refine ⟨50978027505050471968667149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67970703340067295958222865 50978027505050471968667149)
              ·
                refine ⟨19116760314393926988250181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50978027505050471968667149 19116760314393926988250181)
                ·
                  refine ⟨3584392558948861310296909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19116760314393926988250181 3584392558948861310296909)
                  ·
                    refine ⟨1344147209605822991361341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3584392558948861310296909 1344147209605822991361341)
                    ·
                      rfl

theorem cell22_3926576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 4, 3].length) (baseStart_3926576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926576 prefixEnd_3926576 := by exact prefixLift 3926576
  have htrace : WordTrace (prefixWord ++ tailWord_3926576) baseStart_3926576 baseEnd_3926576 := by
    simpa [prefixWord, tailWord_3926576, baseEnd_3926576] using wordTrace_append hprefix tailTrace_3926576
  have hstable : (prefixWord ++ tailWord_3926576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926576).length < 2 ^ (prefixWord ++ tailWord_3926576).sum := by decide
  have hdescent : baseEnd_3926576 < baseStart_3926576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926593 : List Nat := [1, 2, 5, 1, 1, 3, 2, 1, 1, 5]
def baseStart_3926593 : Nat := 118140960795 + 3926593 * 2 ^ 59
def prefixEnd_3926593 : Nat := 4983230072969 + 3 ^ 40 * 3926593 * 2
def baseEnd_3926593 : Nat := 1344153029053240613686289

theorem tailTrace_3926593 : CollatzResearch.WordTrace tailWord_3926593 prefixEnd_3926593 1344153029053240613686289 := by
  unfold tailWord_3926593
  simp only [CollatzResearch.WordTrace]
  refine ⟨143214612263631644539624433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95476408175754429693082955 143214612263631644539624433)
  ·
    refine ⟨107410959197723733404718325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143214612263631644539624433 107410959197723733404718325)
    ·
      refine ⟨10069777424786600006692343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107410959197723733404718325 10069777424786600006692343)
      ·
        refine ⟨15104666137179900010038515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10069777424786600006692343 15104666137179900010038515)
        ·
          refine ⟨22656999205769850015057773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15104666137179900010038515 22656999205769850015057773)
          ·
            refine ⟨8496374702163693755646665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22656999205769850015057773 8496374702163693755646665)
            ·
              refine ⟨6372281026622770316734999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8496374702163693755646665 6372281026622770316734999)
              ·
                refine ⟨9558421539934155475102499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6372281026622770316734999 9558421539934155475102499)
                ·
                  refine ⟨14337632309901233212653749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9558421539934155475102499 14337632309901233212653749)
                  ·
                    refine ⟨1344153029053240613686289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14337632309901233212653749 1344153029053240613686289)
                    ·
                      rfl

theorem cell22_3926593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_3926593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926593 prefixEnd_3926593 := by exact prefixLift 3926593
  have htrace : WordTrace (prefixWord ++ tailWord_3926593) baseStart_3926593 baseEnd_3926593 := by
    simpa [prefixWord, tailWord_3926593, baseEnd_3926593] using wordTrace_append hprefix tailTrace_3926593
  have hstable : (prefixWord ++ tailWord_3926593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926593).length < 2 ^ (prefixWord ++ tailWord_3926593).sum := by decide
  have hdescent : baseEnd_3926593 < baseStart_3926593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926689 : List Nat := [1, 2, 3, 3, 3, 1, 3, 2, 1, 3]
def baseStart_3926689 : Nat := 118140960795 + 3926689 * 2 ^ 59
def prefixEnd_3926689 : Nat := 4983230072969 + 3 ^ 40 * 3926689 * 2
def baseEnd_3926689 : Nat := 1344185891815128363285995

theorem tailTrace_3926689 : CollatzResearch.WordTrace tailWord_3926689 prefixEnd_3926689 1344185891815128363285995 := by
  unfold tailWord_3926689
  simp only [CollatzResearch.WordTrace]
  refine ⟨143218113671283852935119121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95478742447522568623412747 143218113671283852935119121)
  ·
    refine ⟨107413585253462889701339341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143218113671283852935119121 107413585253462889701339341)
    ·
      refine ⟨40280094470048583638002253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107413585253462889701339341 40280094470048583638002253)
      ·
        refine ⟨15105035426268218864250845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40280094470048583638002253 15105035426268218864250845)
        ·
          refine ⟨5664388284850582074094067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15105035426268218864250845 5664388284850582074094067)
          ·
            refine ⟨8496582427275873111141101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5664388284850582074094067 8496582427275873111141101)
            ·
              refine ⟨3186218410228452416677913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8496582427275873111141101 3186218410228452416677913)
              ·
                refine ⟨2389663807671339312508435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3186218410228452416677913 2389663807671339312508435)
                ·
                  refine ⟨3584495711507008968762653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2389663807671339312508435 3584495711507008968762653)
                  ·
                    refine ⟨1344185891815128363285995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3584495711507008968762653 1344185891815128363285995)
                    ·
                      rfl

theorem cell22_3926689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_3926689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926689 prefixEnd_3926689 := by exact prefixLift 3926689
  have htrace : WordTrace (prefixWord ++ tailWord_3926689) baseStart_3926689 baseEnd_3926689 := by
    simpa [prefixWord, tailWord_3926689, baseEnd_3926689] using wordTrace_append hprefix tailTrace_3926689
  have hstable : (prefixWord ++ tailWord_3926689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926689).length < 2 ^ (prefixWord ++ tailWord_3926689).sum := by decide
  have hdescent : baseEnd_3926689 < baseStart_3926689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926702 : List Nat := [4, 1, 4, 1, 1, 1, 4, 1, 5]
def baseStart_3926702 : Nat := 118140960795 + 3926702 * 2 ^ 59
def prefixEnd_3926702 : Nat := 4983230072969 + 3 ^ 40 * 3926702 * 2
def baseEnd_3926702 : Nat := 448063447326933554236985

theorem tailTrace_3926702 : CollatzResearch.WordTrace tailWord_3926702 prefixEnd_3926702 448063447326933554236985 := by
  unfold tailWord_3926702
  simp only [CollatzResearch.WordTrace]
  refine ⟨17902323477529594519417795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95479058546824504103561573 17902323477529594519417795)
  ·
    refine ⟨26853485216294391779126693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17902323477529594519417795 26853485216294391779126693)
    ·
      refine ⟨5035028478055198458586255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26853485216294391779126693 5035028478055198458586255)
      ·
        refine ⟨7552542717082797687879383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5035028478055198458586255 7552542717082797687879383)
        ·
          refine ⟨11328814075624196531819075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7552542717082797687879383 11328814075624196531819075)
          ·
            refine ⟨16993221113436294797728613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11328814075624196531819075 16993221113436294797728613)
            ·
              refine ⟨3186228958769305274574115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16993221113436294797728613 3186228958769305274574115)
              ·
                refine ⟨4779343438153957911861173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3186228958769305274574115 4779343438153957911861173)
                ·
                  refine ⟨448063447326933554236985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4779343438153957911861173 448063447326933554236985)
                  ·
                    rfl

theorem cell22_3926702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_3926702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926702 prefixEnd_3926702 := by exact prefixLift 3926702
  have htrace : WordTrace (prefixWord ++ tailWord_3926702) baseStart_3926702 baseEnd_3926702 := by
    simpa [prefixWord, tailWord_3926702, baseEnd_3926702] using wordTrace_append hprefix tailTrace_3926702
  have hstable : (prefixWord ++ tailWord_3926702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926702).length < 2 ^ (prefixWord ++ tailWord_3926702).sum := by decide
  have hdescent : baseEnd_3926702 < baseStart_3926702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926728 : List Nat := [2, 1, 3, 1, 2, 4, 1, 2, 1, 5]
def baseStart_3926728 : Nat := 118140960795 + 3926728 * 2 ^ 59
def prefixEnd_3926728 : Nat := 4983230072969 + 3 ^ 40 * 3926728 * 2
def baseEnd_3926728 : Nat := 1344199242312145261560875

theorem tailTrace_3926728 : CollatzResearch.WordTrace tailWord_3926728 prefixEnd_3926728 1344199242312145261560875 := by
  unfold tailWord_3926728
  simp only [CollatzResearch.WordTrace]
  refine ⟨71609768059071281297894419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95479690745428375063859225 71609768059071281297894419)
  ·
    refine ⟨107414652088606921946841629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71609768059071281297894419 107414652088606921946841629)
    ·
      refine ⟨40280494533227595730065611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107414652088606921946841629 40280494533227595730065611)
      ·
        refine ⟨60420741799841393595098417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40280494533227595730065611 60420741799841393595098417)
        ·
          refine ⟨45315556349881045196323813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60420741799841393595098417 45315556349881045196323813)
          ·
            refine ⟨8496666815602695974310715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45315556349881045196323813 8496666815602695974310715)
            ·
              refine ⟨12745000223404043961466073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8496666815602695974310715 12745000223404043961466073)
              ·
                refine ⟨9558750167553032971099555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12745000223404043961466073 9558750167553032971099555)
                ·
                  refine ⟨14338125251329549456649333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9558750167553032971099555 14338125251329549456649333)
                  ·
                    refine ⟨1344199242312145261560875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14338125251329549456649333 1344199242312145261560875)
                    ·
                      rfl

theorem cell22_3926728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_3926728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926728 prefixEnd_3926728 := by exact prefixLift 3926728
  have htrace : WordTrace (prefixWord ++ tailWord_3926728) baseStart_3926728 baseEnd_3926728 := by
    simpa [prefixWord, tailWord_3926728, baseEnd_3926728] using wordTrace_append hprefix tailTrace_3926728
  have hstable : (prefixWord ++ tailWord_3926728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926728).length < 2 ^ (prefixWord ++ tailWord_3926728).sum := by decide
  have hdescent : baseEnd_3926728 < baseStart_3926728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926732 : List Nat := [2, 2, 1, 5, 1, 2, 3, 1, 1, 4]
def baseStart_3926732 : Nat := 118140960795 + 3926732 * 2 ^ 59
def prefixEnd_3926732 : Nat := 4983230072969 + 3 ^ 40 * 3926732 * 2
def baseEnd_3926732 : Nat := 1344200611593890584460863

theorem tailTrace_3926732 : CollatzResearch.WordTrace tailWord_3926732 prefixEnd_3926732 1344200611593890584460863 := by
  unfold tailWord_3926732
  simp only [CollatzResearch.WordTrace]
  refine ⟨71609841005064035639467225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95479788006752047519289633 71609841005064035639467225)
  ·
    refine ⟨53707380753798026729600419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71609841005064035639467225 53707380753798026729600419)
    ·
      refine ⟨80561071130697040094400629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53707380753798026729600419 80561071130697040094400629)
      ·
        refine ⟨7552600418502847508850059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80561071130697040094400629 7552600418502847508850059)
        ·
          refine ⟨11328900627754271263275089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7552600418502847508850059 11328900627754271263275089)
          ·
            refine ⟨8496675470815703447456317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11328900627754271263275089 8496675470815703447456317)
            ·
              refine ⟨3186253301555888792796119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8496675470815703447456317 3186253301555888792796119)
              ·
                refine ⟨4779379952333833189194179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3186253301555888792796119 4779379952333833189194179)
                ·
                  refine ⟨7169069928500749783791269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4779379952333833189194179 7169069928500749783791269)
                  ·
                    refine ⟨1344200611593890584460863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7169069928500749783791269 1344200611593890584460863)
                    ·
                      rfl

theorem cell22_3926732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 1, 4].length) (baseStart_3926732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926732 prefixEnd_3926732 := by exact prefixLift 3926732
  have htrace : WordTrace (prefixWord ++ tailWord_3926732) baseStart_3926732 baseEnd_3926732 := by
    simpa [prefixWord, tailWord_3926732, baseEnd_3926732] using wordTrace_append hprefix tailTrace_3926732
  have hstable : (prefixWord ++ tailWord_3926732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926732).length < 2 ^ (prefixWord ++ tailWord_3926732).sum := by decide
  have hdescent : baseEnd_3926732 < baseStart_3926732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926743 : List Nat := [1, 1, 3, 2, 1, 4, 2, 2, 2, 4]
def baseStart_3926743 : Nat := 118140960795 + 3926743 * 2 ^ 59
def prefixEnd_3926743 : Nat := 4983230072969 + 3 ^ 40 * 3926743 * 2
def baseEnd_3926743 : Nat := 1344204377118690222435829

theorem tailTrace_3926743 : CollatzResearch.WordTrace tailWord_3926743 prefixEnd_3926743 1344204377118690222435829 := by
  unfold tailWord_3926743
  simp only [CollatzResearch.WordTrace]
  refine ⟨143220083213088220157584883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95480055475392146771723255 143220083213088220157584883)
  ·
    refine ⟨214830124819632330236377325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143220083213088220157584883 214830124819632330236377325)
    ·
      refine ⟨80561296807362123838641497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214830124819632330236377325 80561296807362123838641497)
      ·
        refine ⟨60420972605521592878981123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80561296807362123838641497 60420972605521592878981123)
        ·
          refine ⟨90631458908282389318471685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60420972605521592878981123 90631458908282389318471685)
          ·
            refine ⟨16993398545302947997213441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90631458908282389318471685 16993398545302947997213441)
            ·
              refine ⟨12745048908977210997910081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16993398545302947997213441 12745048908977210997910081)
              ·
                refine ⟨9558786681732908248432561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12745048908977210997910081 9558786681732908248432561)
                ·
                  refine ⟨7169090011299681186324421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9558786681732908248432561 7169090011299681186324421)
                  ·
                    refine ⟨1344204377118690222435829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7169090011299681186324421 1344204377118690222435829)
                    ·
                      rfl

theorem cell22_3926743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_3926743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926743 prefixEnd_3926743 := by exact prefixLift 3926743
  have htrace : WordTrace (prefixWord ++ tailWord_3926743) baseStart_3926743 baseEnd_3926743 := by
    simpa [prefixWord, tailWord_3926743, baseEnd_3926743] using wordTrace_append hprefix tailTrace_3926743
  have hstable : (prefixWord ++ tailWord_3926743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926743).length < 2 ^ (prefixWord ++ tailWord_3926743).sum := by decide
  have hdescent : baseEnd_3926743 < baseStart_3926743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926745 : List Nat := [1, 2, 1, 2, 3, 2, 4, 2, 2, 3]
def baseStart_3926745 : Nat := 118140960795 + 3926745 * 2 ^ 59
def prefixEnd_3926745 : Nat := 4983230072969 + 3 ^ 40 * 3926745 * 2
def baseEnd_3926745 : Nat := 1344205061759562883885823

theorem tailTrace_3926745 : CollatzResearch.WordTrace tailWord_3926745 prefixEnd_3926745 1344205061759562883885823 := by
  unfold tailWord_3926745
  simp only [CollatzResearch.WordTrace]
  refine ⟨143220156159080974499157689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95480104106053982999438459 143220156159080974499157689)
  ·
    refine ⟨107415117119310730874368267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143220156159080974499157689 107415117119310730874368267)
    ·
      refine ⟨161122675678966096311552401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107415117119310730874368267 161122675678966096311552401)
      ·
        refine ⟨120842006759224572233664301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161122675678966096311552401 120842006759224572233664301)
        ·
          refine ⟨45315752534709214587624113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120842006759224572233664301 45315752534709214587624113)
          ·
            refine ⟨33986814401031910940718085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45315752534709214587624113 33986814401031910940718085)
            ·
              refine ⟨6372527700193483301384641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33986814401031910940718085 6372527700193483301384641)
              ·
                refine ⟨4779395775145112476038481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6372527700193483301384641 4779395775145112476038481)
                ·
                  refine ⟨3584546831358834357028861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4779395775145112476038481 3584546831358834357028861)
                  ·
                    refine ⟨1344205061759562883885823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3584546831358834357028861 1344205061759562883885823)
                    ·
                      rfl

theorem cell22_3926745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 3].length) (baseStart_3926745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926745 prefixEnd_3926745 := by exact prefixLift 3926745
  have htrace : WordTrace (prefixWord ++ tailWord_3926745) baseStart_3926745 baseEnd_3926745 := by
    simpa [prefixWord, tailWord_3926745, baseEnd_3926745] using wordTrace_append hprefix tailTrace_3926745
  have hstable : (prefixWord ++ tailWord_3926745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926745).length < 2 ^ (prefixWord ++ tailWord_3926745).sum := by decide
  have hdescent : baseEnd_3926745 < baseStart_3926745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926771 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 4, 6]
def baseStart_3926771 : Nat := 118140960795 + 3926771 * 2 ^ 59
def prefixEnd_3926771 : Nat := 4983230072969 + 3 ^ 40 * 3926771 * 2
def baseEnd_3926771 : Nat := 1344213962090907482735743

theorem tailTrace_3926771 : CollatzResearch.WordTrace tailWord_3926771 prefixEnd_3926771 1344213962090907482735743 := by
  unfold tailWord_3926771
  simp only [CollatzResearch.WordTrace]
  refine ⟨143221104456986780939604167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95480736304657853959736111 143221104456986780939604167)
  ·
    refine ⟨214831656685480171409406251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143221104456986780939604167 214831656685480171409406251)
    ·
      refine ⟨322247485028220257114109377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214831656685480171409406251 322247485028220257114109377)
      ·
        refine ⟨241685613771165192835582033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322247485028220257114109377 241685613771165192835582033)
        ·
          refine ⟨181264210328373894626686525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241685613771165192835582033 181264210328373894626686525)
          ·
            refine ⟨67974078873140210485007447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181264210328373894626686525 67974078873140210485007447)
            ·
              refine ⟨101961118309710315727511171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67974078873140210485007447 101961118309710315727511171)
              ·
                refine ⟨152941677464565473591266757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101961118309710315727511171 152941677464565473591266757)
                ·
                  refine ⟨28676564524606026298362517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152941677464565473591266757 28676564524606026298362517)
                  ·
                    refine ⟨1344213962090907482735743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28676564524606026298362517 1344213962090907482735743)
                    ·
                      rfl

theorem cell22_3926771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 6].length) (baseStart_3926771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926771 prefixEnd_3926771 := by exact prefixLift 3926771
  have htrace : WordTrace (prefixWord ++ tailWord_3926771) baseStart_3926771 baseEnd_3926771 := by
    simpa [prefixWord, tailWord_3926771, baseEnd_3926771] using wordTrace_append hprefix tailTrace_3926771
  have hstable : (prefixWord ++ tailWord_3926771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926771).length < 2 ^ (prefixWord ++ tailWord_3926771).sum := by decide
  have hdescent : baseEnd_3926771 < baseStart_3926771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926807 : List Nat := [1, 1, 3, 4, 3, 1, 2, 1, 3, 3]
def baseStart_3926807 : Nat := 118140960795 + 3926807 * 2 ^ 59
def prefixEnd_3926807 : Nat := 4983230072969 + 3 ^ 40 * 3926807 * 2
def baseEnd_3926807 : Nat := 1344226285626615388835633

theorem tailTrace_3926807 : CollatzResearch.WordTrace tailWord_3926807 prefixEnd_3926807 1344226285626615388835633 := by
  unfold tailWord_3926807
  simp only [CollatzResearch.WordTrace]
  refine ⟨143222417484856359087914675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95481611656570906058609783 143222417484856359087914675)
  ·
    refine ⟨214833626227284538631872013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143222417484856359087914675 214833626227284538631872013)
    ·
      refine ⟨80562609835231701986952005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214833626227284538631872013 80562609835231701986952005)
      ·
        refine ⟨15105489344105944122553501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80562609835231701986952005 15105489344105944122553501)
        ·
          refine ⟨5664558504039729045957563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15105489344105944122553501 5664558504039729045957563)
          ·
            refine ⟨8496837756059593568936345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5664558504039729045957563 8496837756059593568936345)
            ·
              refine ⟨6372628317044695176702259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8496837756059593568936345 6372628317044695176702259)
              ·
                refine ⟨9558942475567042765053389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6372628317044695176702259 9558942475567042765053389)
                ·
                  refine ⟨3584603428337641036895021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9558942475567042765053389 3584603428337641036895021)
                  ·
                    refine ⟨1344226285626615388835633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3584603428337641036895021 1344226285626615388835633)
                    ·
                      rfl

theorem cell22_3926807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_3926807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926807 prefixEnd_3926807 := by exact prefixLift 3926807
  have htrace : WordTrace (prefixWord ++ tailWord_3926807) baseStart_3926807 baseEnd_3926807 := by
    simpa [prefixWord, tailWord_3926807, baseEnd_3926807] using wordTrace_append hprefix tailTrace_3926807
  have hstable : (prefixWord ++ tailWord_3926807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926807).length < 2 ^ (prefixWord ++ tailWord_3926807).sum := by decide
  have hdescent : baseEnd_3926807 < baseStart_3926807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926910 : List Nat := [4, 2, 3, 1, 12]
def baseStart_3926910 : Nat := 118140960795 + 3926910 * 2 ^ 59
def prefixEnd_3926910 : Nat := 4983230072969 + 3 ^ 40 * 3926910 * 2
def baseEnd_3926910 : Nat := 5531940512887067709919

theorem tailTrace_3926910 : CollatzResearch.WordTrace tailWord_3926910 prefixEnd_3926910 5531940512887067709919 := by
  unfold tailWord_3926910
  simp only [CollatzResearch.WordTrace]
  refine ⟨17903271775435400959864273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95484116135655471785942789 17903271775435400959864273)
  ·
    refine ⟨13427453831576550719898205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17903271775435400959864273 13427453831576550719898205)
    ·
      refine ⟨5035295186841206519961827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13427453831576550719898205 5035295186841206519961827)
      ·
        refine ⟨7552942780261809779942741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5035295186841206519961827 7552942780261809779942741)
        ·
          refine ⟨5531940512887067709919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7552942780261809779942741 5531940512887067709919)
          ·
            rfl

theorem cell22_3926910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 12].length) (baseStart_3926910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926910 prefixEnd_3926910 := by exact prefixLift 3926910
  have htrace : WordTrace (prefixWord ++ tailWord_3926910) baseStart_3926910 baseEnd_3926910 := by
    simpa [prefixWord, tailWord_3926910, baseEnd_3926910] using wordTrace_append hprefix tailTrace_3926910
  have hstable : (prefixWord ++ tailWord_3926910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926910).length < 2 ^ (prefixWord ++ tailWord_3926910).sum := by decide
  have hdescent : baseEnd_3926910 < baseStart_3926910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926923 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 2, 6]
def baseStart_3926923 : Nat := 118140960795 + 3926923 * 2 ^ 59
def prefixEnd_3926923 : Nat := 4983230072969 + 3 ^ 40 * 3926923 * 2
def baseEnd_3926923 : Nat := 1344265994797229752935277

theorem tailTrace_3926923 : CollatzResearch.WordTrace tailWord_3926923 prefixEnd_3926923 1344265994797229752935277 := by
  unfold tailWord_3926923
  simp only [CollatzResearch.WordTrace]
  refine ⟨143226648352436110899137423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95484432234957407266091615 143226648352436110899137423)
  ·
    refine ⟨214839972528654166348706135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143226648352436110899137423 214839972528654166348706135)
    ·
      refine ⟨322259958792981249523059203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214839972528654166348706135 322259958792981249523059203)
      ·
        refine ⟨483389938189471874284588805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322259958792981249523059203 483389938189471874284588805)
        ·
          refine ⟨90635613410525976428360401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 483389938189471874284588805 90635613410525976428360401)
          ·
            refine ⟨67976710057894482321270301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90635613410525976428360401 67976710057894482321270301)
            ·
              refine ⟨25491266271710430870476363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67976710057894482321270301 25491266271710430870476363)
              ·
                refine ⟨38236899407565646305714545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25491266271710430870476363 38236899407565646305714545)
                ·
                  refine ⟨28677674555674234729285909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38236899407565646305714545 28677674555674234729285909)
                  ·
                    refine ⟨1344265994797229752935277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28677674555674234729285909 1344265994797229752935277)
                    ·
                      rfl

theorem cell22_3926923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 6].length) (baseStart_3926923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926923 prefixEnd_3926923 := by exact prefixLift 3926923
  have htrace : WordTrace (prefixWord ++ tailWord_3926923) baseStart_3926923 baseEnd_3926923 := by
    simpa [prefixWord, tailWord_3926923, baseEnd_3926923] using wordTrace_append hprefix tailTrace_3926923
  have hstable : (prefixWord ++ tailWord_3926923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926923).length < 2 ^ (prefixWord ++ tailWord_3926923).sum := by decide
  have hdescent : baseEnd_3926923 < baseStart_3926923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926953 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 1, 7]
def baseStart_3926953 : Nat := 118140960795 + 3926953 * 2 ^ 59
def prefixEnd_3926953 : Nat := 4983230072969 + 3 ^ 40 * 3926953 * 2
def baseEnd_3926953 : Nat := 1344276264410319674685185

theorem tailTrace_3926953 : CollatzResearch.WordTrace tailWord_3926953 prefixEnd_3926953 1344276264410319674685185 := by
  unfold tailWord_3926953
  simp only [CollatzResearch.WordTrace]
  refine ⟨143227742542327426022729513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95485161694884950681819675 143227742542327426022729513)
  ·
    refine ⟨107420806906745569517047135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143227742542327426022729513 107420806906745569517047135)
    ·
      refine ⟨161131210360118354275570703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107420806906745569517047135 161131210360118354275570703)
      ·
        refine ⟨241696815540177531413356055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161131210360118354275570703 241696815540177531413356055)
        ·
          refine ⟨362545223310266297120034083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241696815540177531413356055 362545223310266297120034083)
          ·
            refine ⟨543817834965399445680051125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362545223310266297120034083 543817834965399445680051125)
            ·
              refine ⟨50982922028006198032504793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 543817834965399445680051125 50982922028006198032504793)
              ·
                refine ⟨38237191521004648524378595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50982922028006198032504793 38237191521004648524378595)
                ·
                  refine ⟨57355787281506972786567893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38237191521004648524378595 57355787281506972786567893)
                  ·
                    refine ⟨1344276264410319674685185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57355787281506972786567893 1344276264410319674685185)
                    ·
                      rfl

theorem cell22_3926953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_3926953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926953 prefixEnd_3926953 := by exact prefixLift 3926953
  have htrace : WordTrace (prefixWord ++ tailWord_3926953) baseStart_3926953 baseEnd_3926953 := by
    simpa [prefixWord, tailWord_3926953, baseEnd_3926953] using wordTrace_append hprefix tailTrace_3926953
  have hstable : (prefixWord ++ tailWord_3926953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926953).length < 2 ^ (prefixWord ++ tailWord_3926953).sum := by decide
  have hdescent : baseEnd_3926953 < baseStart_3926953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926982 : List Nat := [6, 1, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3926982 : Nat := 118140960795 + 3926982 * 2 ^ 59
def prefixEnd_3926982 : Nat := 4983230072969 + 3 ^ 40 * 3926982 * 2
def baseEnd_3926982 : Nat := 1344286191702973265710097

theorem tailTrace_3926982 : CollatzResearch.WordTrace tailWord_3926982 prefixEnd_3926982 1344286191702973265710097 := by
  unfold tailWord_3926982
  simp only [CollatzResearch.WordTrace]
  refine ⟨4475900008100698874235475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95485866839481575983690133 4475900008100698874235475)
  ·
    refine ⟨6713850012151048311353213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4475900008100698874235475 6713850012151048311353213)
    ·
      refine ⟨2517693754556643116757455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6713850012151048311353213 2517693754556643116757455)
      ·
        refine ⟨3776540631834964675136183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2517693754556643116757455 3776540631834964675136183)
        ·
          refine ⟨5664810947752447012704275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3776540631834964675136183 5664810947752447012704275)
          ·
            refine ⟨8497216421628670519056413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5664810947752447012704275 8497216421628670519056413)
            ·
              refine ⟨3186456158110751444646155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8497216421628670519056413 3186456158110751444646155)
              ·
                refine ⟨4779684237166127166969233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3186456158110751444646155 4779684237166127166969233)
                ·
                  refine ⟨3584763177874595375226925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4779684237166127166969233 3584763177874595375226925)
                  ·
                    refine ⟨1344286191702973265710097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3584763177874595375226925 1344286191702973265710097)
                    ·
                      rfl

theorem cell22_3926982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3926982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3926982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3926982 prefixEnd_3926982 := by exact prefixLift 3926982
  have htrace : WordTrace (prefixWord ++ tailWord_3926982) baseStart_3926982 baseEnd_3926982 := by
    simpa [prefixWord, tailWord_3926982, baseEnd_3926982] using wordTrace_append hprefix tailTrace_3926982
  have hstable : (prefixWord ++ tailWord_3926982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926982).length < 2 ^ (prefixWord ++ tailWord_3926982).sum := by decide
  have hdescent : baseEnd_3926982 < baseStart_3926982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927000 : List Nat := [2, 1, 2, 2, 2, 3, 2, 2, 6]
def baseStart_3927000 : Nat := 118140960795 + 3927000 * 2 ^ 59
def prefixEnd_3927000 : Nat := 4983230072969 + 3 ^ 40 * 3927000 * 2
def baseEnd_3927000 : Nat := 448097451156942406253347

theorem tailTrace_3927000 : CollatzResearch.WordTrace tailWord_3927000 prefixEnd_3927000 448097451156942406253347 := by
  unfold tailWord_3927000
  simp only [CollatzResearch.WordTrace]
  refine ⟨71614728386578576524845227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95486304515438102033126969 71614728386578576524845227)
  ·
    refine ⟨107422092579867864787267841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71614728386578576524845227 107422092579867864787267841)
    ·
      refine ⟨80566569434900898590450881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107422092579867864787267841 80566569434900898590450881)
      ·
        refine ⟨60424927076175673942838161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80566569434900898590450881 60424927076175673942838161)
        ·
          refine ⟨45318695307131755457128621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60424927076175673942838161 45318695307131755457128621)
          ·
            refine ⟨16994510740174408296423233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45318695307131755457128621 16994510740174408296423233)
            ·
              refine ⟨12745883055130806222317425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16994510740174408296423233 12745883055130806222317425)
              ·
                refine ⟨9559412291348104666738069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12745883055130806222317425 9559412291348104666738069)
                ·
                  refine ⟨448097451156942406253347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9559412291348104666738069 448097451156942406253347)
                  ·
                    rfl

theorem cell22_3927000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 6].length) (baseStart_3927000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927000 prefixEnd_3927000 := by exact prefixLift 3927000
  have htrace : WordTrace (prefixWord ++ tailWord_3927000) baseStart_3927000 baseEnd_3927000 := by
    simpa [prefixWord, tailWord_3927000, baseEnd_3927000] using wordTrace_append hprefix tailTrace_3927000
  have hstable : (prefixWord ++ tailWord_3927000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927000).length < 2 ^ (prefixWord ++ tailWord_3927000).sum := by decide
  have hdescent : baseEnd_3927000 < baseStart_3927000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927002 : List Nat := [3, 1, 1, 2, 4, 1, 1, 4, 1, 4]
def baseStart_3927002 : Nat := 118140960795 + 3927002 * 2 ^ 59
def prefixEnd_3927002 : Nat := 4983230072969 + 3 ^ 40 * 3927002 * 2
def baseEnd_3927002 : Nat := 1344293038111699880210035

theorem tailTrace_3927002 : CollatzResearch.WordTrace tailWord_3927002 prefixEnd_3927002 1344293038111699880210035 := by
  unfold tailWord_3927002
  simp only [CollatzResearch.WordTrace]
  refine ⟨35807382429787476847815815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95486353146099938260842173 35807382429787476847815815)
  ·
    refine ⟨53711073644681215271723723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35807382429787476847815815 53711073644681215271723723)
    ·
      refine ⟨80566610467021822907585585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53711073644681215271723723 80566610467021822907585585)
      ·
        refine ⟨60424957850266367180689189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80566610467021822907585585 60424957850266367180689189)
        ·
          refine ⟨11329679596924943846379223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60424957850266367180689189 11329679596924943846379223)
          ·
            refine ⟨16994519395387415769568835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11329679596924943846379223 16994519395387415769568835)
            ·
              refine ⟨25491779093081123654353253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16994519395387415769568835 25491779093081123654353253)
              ·
                refine ⟨4779708579952710685191235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25491779093081123654353253 4779708579952710685191235)
                ·
                  refine ⟨7169562869929066027786853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4779708579952710685191235 7169562869929066027786853)
                  ·
                    refine ⟨1344293038111699880210035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7169562869929066027786853 1344293038111699880210035)
                    ·
                      rfl

theorem cell22_3927002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_3927002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927002 prefixEnd_3927002 := by exact prefixLift 3927002
  have htrace : WordTrace (prefixWord ++ tailWord_3927002) baseStart_3927002 baseEnd_3927002 := by
    simpa [prefixWord, tailWord_3927002, baseEnd_3927002] using wordTrace_append hprefix tailTrace_3927002
  have hstable : (prefixWord ++ tailWord_3927002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927002).length < 2 ^ (prefixWord ++ tailWord_3927002).sum := by decide
  have hdescent : baseEnd_3927002 < baseStart_3927002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927032 : List Nat := [2, 1, 2, 1, 1, 3, 1, 6, 2, 3]
def baseStart_3927032 : Nat := 118140960795 + 3927032 * 2 ^ 59
def prefixEnd_3927032 : Nat := 4983230072969 + 3 ^ 40 * 3927032 * 2
def baseEnd_3927032 : Nat := 1344303307724789801959943

theorem tailTrace_3927032 : CollatzResearch.WordTrace tailWord_3927032 prefixEnd_3927032 1344303307724789801959943 := by
  unfold tailWord_3927032
  simp only [CollatzResearch.WordTrace]
  refine ⟨71615311954520611257427675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95487082606027481676570233 71615311954520611257427675)
  ·
    refine ⟨107422967931780916886141513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71615311954520611257427675 107422967931780916886141513)
    ·
      refine ⟨80567225948835687664606135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107422967931780916886141513 80567225948835687664606135)
      ·
        refine ⟨120850838923253531496909203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80567225948835687664606135 120850838923253531496909203)
        ·
          refine ⟨181276258384880297245363805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120850838923253531496909203 181276258384880297245363805)
          ·
            refine ⟨67978596894330111467011427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181276258384880297245363805 67978596894330111467011427)
            ·
              refine ⟨101967895341495167200517141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67978596894330111467011427 101967895341495167200517141)
              ·
                refine ⟨4779745094132585962524241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101967895341495167200517141 4779745094132585962524241)
                ·
                  refine ⟨3584808820599439471893181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4779745094132585962524241 3584808820599439471893181)
                  ·
                    refine ⟨1344303307724789801959943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3584808820599439471893181 1344303307724789801959943)
                    ·
                      rfl

theorem cell22_3927032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_3927032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927032 prefixEnd_3927032 := by exact prefixLift 3927032
  have htrace : WordTrace (prefixWord ++ tailWord_3927032) baseStart_3927032 baseEnd_3927032 := by
    simpa [prefixWord, tailWord_3927032, baseEnd_3927032] using wordTrace_append hprefix tailTrace_3927032
  have hstable : (prefixWord ++ tailWord_3927032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927032).length < 2 ^ (prefixWord ++ tailWord_3927032).sum := by decide
  have hdescent : baseEnd_3927032 < baseStart_3927032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927045 : List Nat := [1, 3, 1, 1, 2, 3, 4, 7]
def baseStart_3927045 : Nat := 118140960795 + 3927045 * 2 ^ 59
def prefixEnd_3927045 : Nat := 4983230072969 + 3 ^ 40 * 3927045 * 2
def baseEnd_3927045 : Nat := 149367528654495789042767

theorem tailTrace_3927045 : CollatzResearch.WordTrace tailWord_3927045 prefixEnd_3927045 149367528654495789042767 := by
  unfold tailWord_3927045
  simp only [CollatzResearch.WordTrace]
  refine ⟨143231098057994125735078589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95487398705329417156719059 143231098057994125735078589)
  ·
    refine ⟨53711661771747797150654471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143231098057994125735078589 53711661771747797150654471)
    ·
      refine ⟨80567492657621695725981707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53711661771747797150654471 80567492657621695725981707)
      ·
        refine ⟨120851238986432543588972561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80567492657621695725981707 120851238986432543588972561)
        ·
          refine ⟨90638429239824407691729421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120851238986432543588972561 90638429239824407691729421)
          ·
            refine ⟨33989410964934152884398533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90638429239824407691729421 33989410964934152884398533)
            ·
              refine ⟨6373014555925153665824725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33989410964934152884398533 6373014555925153665824725)
              ·
                refine ⟨149367528654495789042767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6373014555925153665824725 149367528654495789042767)
                ·
                  rfl

theorem cell22_3927045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 7].length) (baseStart_3927045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927045 prefixEnd_3927045 := by exact prefixLift 3927045
  have htrace : WordTrace (prefixWord ++ tailWord_3927045) baseStart_3927045 baseEnd_3927045 := by
    simpa [prefixWord, tailWord_3927045, baseEnd_3927045] using wordTrace_append hprefix tailTrace_3927045
  have hstable : (prefixWord ++ tailWord_3927045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927045).length < 2 ^ (prefixWord ++ tailWord_3927045).sum := by decide
  have hdescent : baseEnd_3927045 < baseStart_3927045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927135 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 8]
def baseStart_3927135 : Nat := 118140960795 + 3927135 * 2 ^ 59
def prefixEnd_3927135 : Nat := 4983230072969 + 3 ^ 40 * 3927135 * 2
def baseEnd_3927135 : Nat := 448112855576577288878209

theorem tailTrace_3927135 : CollatzResearch.WordTrace tailWord_3927135 prefixEnd_3927135 448112855576577288878209 := by
  unfold tailWord_3927135
  simp only [CollatzResearch.WordTrace]
  refine ⟨143234380627668071105854859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95489587085112047403903239 143234380627668071105854859)
  ·
    refine ⟨214851570941502106658782289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143234380627668071105854859 214851570941502106658782289)
    ·
      refine ⟨161138678206126579994086717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214851570941502106658782289 161138678206126579994086717)
      ·
        refine ⟨60427004327297467497782519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161138678206126579994086717 60427004327297467497782519)
        ·
          refine ⟨90640506490946201246673779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60427004327297467497782519 90640506490946201246673779)
          ·
            refine ⟨135960759736419301870010669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90640506490946201246673779 135960759736419301870010669)
            ·
              refine ⟨50985284901157238201254001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135960759736419301870010669 50985284901157238201254001)
              ·
                refine ⟨38238963675867928650940501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50985284901157238201254001 38238963675867928650940501)
                ·
                  refine ⟨448112855576577288878209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38238963675867928650940501 448112855576577288878209)
                  ·
                    rfl

theorem cell22_3927135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 8].length) (baseStart_3927135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927135 prefixEnd_3927135 := by exact prefixLift 3927135
  have htrace : WordTrace (prefixWord ++ tailWord_3927135) baseStart_3927135 baseEnd_3927135 := by
    simpa [prefixWord, tailWord_3927135, baseEnd_3927135] using wordTrace_append hprefix tailTrace_3927135
  have hstable : (prefixWord ++ tailWord_3927135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927135).length < 2 ^ (prefixWord ++ tailWord_3927135).sum := by decide
  have hdescent : baseEnd_3927135 < baseStart_3927135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927152 : List Nat := [2, 1, 1, 1, 5, 1, 4, 1, 6]
def baseStart_3927152 : Nat := 118140960795 + 3927152 * 2 ^ 59
def prefixEnd_3927152 : Nat := 4983230072969 + 3 ^ 40 * 3927152 * 2
def baseEnd_3927152 : Nat := 448114795392383162986525

theorem tailTrace_3927152 : CollatzResearch.WordTrace tailWord_3927152 prefixEnd_3927152 448114795392383162986525 := by
  unfold tailWord_3927152
  simp only [CollatzResearch.WordTrace]
  refine ⟨71617500334303241504611855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95490000445737655339482473 71617500334303241504611855)
  ·
    refine ⟨107426250501454862256917783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71617500334303241504611855 107426250501454862256917783)
    ·
      refine ⟨161139375752182293385376675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107426250501454862256917783 161139375752182293385376675)
      ·
        refine ⟨241709063628273440078065013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161139375752182293385376675 241709063628273440078065013)
        ·
          refine ⟨22660224715150635007318595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241709063628273440078065013 22660224715150635007318595)
          ·
            refine ⟨33990337072725952510977893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22660224715150635007318595 33990337072725952510977893)
            ·
              refine ⟨6373188201136116095808355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33990337072725952510977893 6373188201136116095808355)
              ·
                refine ⟨9559782301704174143712533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6373188201136116095808355 9559782301704174143712533)
                ·
                  refine ⟨448114795392383162986525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9559782301704174143712533 448114795392383162986525)
                  ·
                    rfl

theorem cell22_3927152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 6].length) (baseStart_3927152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927152 prefixEnd_3927152 := by exact prefixLift 3927152
  have htrace : WordTrace (prefixWord ++ tailWord_3927152) baseStart_3927152 baseEnd_3927152 := by
    simpa [prefixWord, tailWord_3927152, baseEnd_3927152] using wordTrace_append hprefix tailTrace_3927152
  have hstable : (prefixWord ++ tailWord_3927152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927152).length < 2 ^ (prefixWord ++ tailWord_3927152).sum := by decide
  have hdescent : baseEnd_3927152 < baseStart_3927152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927186 : List Nat := [3, 2, 3, 1, 1, 2, 3, 3, 4]
def baseStart_3927186 : Nat := 118140960795 + 3927186 * 2 ^ 59
def prefixEnd_3927186 : Nat := 4983230072969 + 3 ^ 40 * 3927186 * 2
def baseEnd_3927186 : Nat := 448118675023994911203157

theorem tailTrace_3927186 : CollatzResearch.WordTrace tailWord_3927186 prefixEnd_3927186 448118675023994911203157 := by
  unfold tailWord_3927186
  simp only [CollatzResearch.WordTrace]
  refine ⟨35809060187620826703990353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95490827166988871210640941 35809060187620826703990353)
  ·
    refine ⟨26856795140715620027992765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35809060187620826703990353 26856795140715620027992765)
    ·
      refine ⟨10071298177768357510497287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26856795140715620027992765 10071298177768357510497287)
      ·
        refine ⟨15106947266652536265745931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10071298177768357510497287 15106947266652536265745931)
        ·
          refine ⟨22660420899978804398618897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15106947266652536265745931 22660420899978804398618897)
          ·
            refine ⟨16995315674984103298964173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22660420899978804398618897 16995315674984103298964173)
            ·
              refine ⟨6373243378119038737111565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16995315674984103298964173 6373243378119038737111565)
              ·
                refine ⟨2389966266794639526416837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6373243378119038737111565 2389966266794639526416837)
                ·
                  refine ⟨448118675023994911203157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2389966266794639526416837 448118675023994911203157)
                  ·
                    rfl

theorem cell22_3927186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_3927186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927186 prefixEnd_3927186 := by exact prefixLift 3927186
  have htrace : WordTrace (prefixWord ++ tailWord_3927186) baseStart_3927186 baseEnd_3927186 := by
    simpa [prefixWord, tailWord_3927186, baseEnd_3927186] using wordTrace_append hprefix tailTrace_3927186
  have hstable : (prefixWord ++ tailWord_3927186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927186).length < 2 ^ (prefixWord ++ tailWord_3927186).sum := by decide
  have hdescent : baseEnd_3927186 < baseStart_3927186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927218 : List Nat := [3, 2, 1, 1, 1, 6, 2, 1, 2, 3]
def baseStart_3927218 : Nat := 118140960795 + 3927218 * 2 ^ 59
def prefixEnd_3927218 : Nat := 4983230072969 + 3 ^ 40 * 3927218 * 2
def baseEnd_3927218 : Nat := 1344366979325947316809373

theorem tailTrace_3927218 : CollatzResearch.WordTrace tailWord_3927218 prefixEnd_3927218 1344366979325947316809373 := by
  unfold tailWord_3927218
  simp only [CollatzResearch.WordTrace]
  refine ⟨35809351971591844070281577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95491605257578250854084205 35809351971591844070281577)
  ·
    refine ⟨26857013978693883052711183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35809351971591844070281577 26857013978693883052711183)
    ·
      refine ⟨40285520968040824579066775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26857013978693883052711183 40285520968040824579066775)
      ·
        refine ⟨60428281452061236868600163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40285520968040824579066775 60428281452061236868600163)
        ·
          refine ⟨90642422178091855302900245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60428281452061236868600163 90642422178091855302900245)
          ·
            refine ⟨4248863539598055717323449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90642422178091855302900245 4248863539598055717323449)
            ·
              refine ⟨3186647654698541787992587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4248863539598055717323449 3186647654698541787992587)
              ·
                refine ⟨4779971482047812681988881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3186647654698541787992587 4779971482047812681988881)
                ·
                  refine ⟨3584978611535859511491661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4779971482047812681988881 3584978611535859511491661)
                  ·
                    refine ⟨1344366979325947316809373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3584978611535859511491661 1344366979325947316809373)
                    ·
                      rfl

theorem cell22_3927218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_3927218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927218 prefixEnd_3927218 := by exact prefixLift 3927218
  have htrace : WordTrace (prefixWord ++ tailWord_3927218) baseStart_3927218 baseEnd_3927218 := by
    simpa [prefixWord, tailWord_3927218, baseEnd_3927218] using wordTrace_append hprefix tailTrace_3927218
  have hstable : (prefixWord ++ tailWord_3927218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927218).length < 2 ^ (prefixWord ++ tailWord_3927218).sum := by decide
  have hdescent : baseEnd_3927218 < baseStart_3927218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927222 : List Nat := [5, 1, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_3927222 : Nat := 118140960795 + 3927222 * 2 ^ 59
def prefixEnd_3927222 : Nat := 4983230072969 + 3 ^ 40 * 3927222 * 2
def baseEnd_3927222 : Nat := 1344368348607692639709361

theorem tailTrace_3927222 : CollatzResearch.WordTrace tailWord_3927222 prefixEnd_3927222 1344368348607692639709361 := by
  unfold tailWord_3927222
  simp only [CollatzResearch.WordTrace]
  refine ⟨8952347111147055310266995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95491702518901923309514613 8952347111147055310266995)
  ·
    refine ⟨13428520666720582965400493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8952347111147055310266995 13428520666720582965400493)
    ·
      refine ⟨5035695250020218612025185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13428520666720582965400493 5035695250020218612025185)
      ·
        refine ⟨3776771437515163959018889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5035695250020218612025185 3776771437515163959018889)
        ·
          refine ⟨2832578578136372969264167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3776771437515163959018889 2832578578136372969264167)
          ·
            refine ⟨4248867867204559453896251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2832578578136372969264167 4248867867204559453896251)
            ·
              refine ⟨6373301800806839180844377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4248867867204559453896251 6373301800806839180844377)
              ·
                refine ⟨4779976350605129385633283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6373301800806839180844377 4779976350605129385633283)
                ·
                  refine ⟨7169964525907694078449925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4779976350605129385633283 7169964525907694078449925)
                  ·
                    refine ⟨1344368348607692639709361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7169964525907694078449925 1344368348607692639709361)
                    ·
                      rfl

theorem cell22_3927222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_3927222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927222 prefixEnd_3927222 := by exact prefixLift 3927222
  have htrace : WordTrace (prefixWord ++ tailWord_3927222) baseStart_3927222 baseEnd_3927222 := by
    simpa [prefixWord, tailWord_3927222, baseEnd_3927222] using wordTrace_append hprefix tailTrace_3927222
  have hstable : (prefixWord ++ tailWord_3927222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927222).length < 2 ^ (prefixWord ++ tailWord_3927222).sum := by decide
  have hdescent : baseEnd_3927222 < baseStart_3927222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927229 : List Nat := [1, 4, 1, 2, 1, 1, 2, 4, 3, 3]
def baseStart_3927229 : Nat := 118140960795 + 3927229 * 2 ^ 59
def prefixEnd_3927229 : Nat := 4983230072969 + 3 ^ 40 * 3927229 * 2
def baseEnd_3927229 : Nat := 1344370744850746954784339

theorem tailTrace_3927229 : CollatzResearch.WordTrace tailWord_3927229 prefixEnd_3927229 1344370744850746954784339 := by
  unfold tailWord_3927229
  simp only [CollatzResearch.WordTrace]
  refine ⟨143237809089327525159776741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95491872726218350106517827 143237809089327525159776741)
  ·
    refine ⟨26857089204248910967458139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143237809089327525159776741 26857089204248910967458139)
    ·
      refine ⟨40285633806373366451187209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26857089204248910967458139 40285633806373366451187209)
      ·
        refine ⟨30214225354780024838390407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40285633806373366451187209 30214225354780024838390407)
        ·
          refine ⟨45321338032170037257585611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30214225354780024838390407 45321338032170037257585611)
          ·
            refine ⟨67982007048255055886378417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45321338032170037257585611 67982007048255055886378417)
            ·
              refine ⟨50986505286191291914783813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67982007048255055886378417 50986505286191291914783813)
              ·
                refine ⟨9559969741160867234021965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50986505286191291914783813 9559969741160867234021965)
                ·
                  refine ⟨3584988652935325212758237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9559969741160867234021965 3584988652935325212758237)
                  ·
                    refine ⟨1344370744850746954784339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3584988652935325212758237 1344370744850746954784339)
                    ·
                      rfl

theorem cell22_3927229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_3927229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927229 prefixEnd_3927229 := by exact prefixLift 3927229
  have htrace : WordTrace (prefixWord ++ tailWord_3927229) baseStart_3927229 baseEnd_3927229 := by
    simpa [prefixWord, tailWord_3927229, baseEnd_3927229] using wordTrace_append hprefix tailTrace_3927229
  have hstable : (prefixWord ++ tailWord_3927229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927229).length < 2 ^ (prefixWord ++ tailWord_3927229).sum := by decide
  have hdescent : baseEnd_3927229 < baseStart_3927229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927257 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 2, 5]
def baseStart_3927257 : Nat := 118140960795 + 3927257 * 2 ^ 59
def prefixEnd_3927257 : Nat := 4983230072969 + 3 ^ 40 * 3927257 * 2
def baseEnd_3927257 : Nat := 1344380329822964215084253

theorem tailTrace_3927257 : CollatzResearch.WordTrace tailWord_3927257 prefixEnd_3927257 1344380329822964215084253 := by
  unfold tailWord_3927257
  simp only [CollatzResearch.WordTrace]
  refine ⟨143238830333226085941796025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95492553555484057294530683 143238830333226085941796025)
  ·
    refine ⟨107429122749919564456347019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143238830333226085941796025 107429122749919564456347019)
    ·
      refine ⟨161143684124879346684520529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107429122749919564456347019 161143684124879346684520529)
      ·
        refine ⟨120857763093659510013390397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161143684124879346684520529 120857763093659510013390397)
        ·
          refine ⟨45321661160122316255021399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120857763093659510013390397 45321661160122316255021399)
          ·
            refine ⟨67982491740183474382532099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45321661160122316255021399 67982491740183474382532099)
            ·
              refine ⟨101973737610275211573798149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67982491740183474382532099 101973737610275211573798149)
              ·
                refine ⟨19120075801926602170087153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101973737610275211573798149 19120075801926602170087153)
                ·
                  refine ⟨14340056851444951627565365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19120075801926602170087153 14340056851444951627565365)
                  ·
                    refine ⟨1344380329822964215084253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14340056851444951627565365 1344380329822964215084253)
                    ·
                      rfl

theorem cell22_3927257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_3927257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927257 prefixEnd_3927257 := by exact prefixLift 3927257
  have htrace : WordTrace (prefixWord ++ tailWord_3927257) baseStart_3927257 baseEnd_3927257 := by
    simpa [prefixWord, tailWord_3927257, baseEnd_3927257] using wordTrace_append hprefix tailTrace_3927257
  have hstable : (prefixWord ++ tailWord_3927257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927257).length < 2 ^ (prefixWord ++ tailWord_3927257).sum := by decide
  have hdescent : baseEnd_3927257 < baseStart_3927257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927263 : List Nat := [1, 1, 2, 3, 2, 1, 6, 2, 1, 3]
def baseStart_3927263 : Nat := 118140960795 + 3927263 * 2 ^ 59
def prefixEnd_3927263 : Nat := 4983230072969 + 3 ^ 40 * 3927263 * 2
def baseEnd_3927263 : Nat := 1344382383745582199434235

theorem tailTrace_3927263 : CollatzResearch.WordTrace tailWord_3927263 prefixEnd_3927263 1344382383745582199434235 := by
  unfold tailWord_3927263
  simp only [CollatzResearch.WordTrace]
  refine ⟨143239049171204348966514443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95492699447469565977676295 143239049171204348966514443)
  ·
    refine ⟨214858573756806523449771665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143239049171204348966514443 214858573756806523449771665)
    ·
      refine ⟨161143930317604892587328749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214858573756806523449771665 161143930317604892587328749)
      ·
        refine ⟨60428973869101834720248281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161143930317604892587328749 60428973869101834720248281)
        ·
          refine ⟨45321730401826376040186211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60428973869101834720248281 45321730401826376040186211)
          ·
            refine ⟨67982595602739564060279317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45321730401826376040186211 67982595602739564060279317)
            ·
              refine ⟨3186684168878417065325593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67982595602739564060279317 3186684168878417065325593)
              ·
                refine ⟨2390013126658812798994195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3186684168878417065325593 2390013126658812798994195)
                ·
                  refine ⟨3585019689988219198491293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2390013126658812798994195 3585019689988219198491293)
                  ·
                    refine ⟨1344382383745582199434235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3585019689988219198491293 1344382383745582199434235)
                    ·
                      rfl

theorem cell22_3927263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 1, 3].length) (baseStart_3927263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927263 prefixEnd_3927263 := by exact prefixLift 3927263
  have htrace : WordTrace (prefixWord ++ tailWord_3927263) baseStart_3927263 baseEnd_3927263 := by
    simpa [prefixWord, tailWord_3927263, baseEnd_3927263] using wordTrace_append hprefix tailTrace_3927263
  have hstable : (prefixWord ++ tailWord_3927263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927263).length < 2 ^ (prefixWord ++ tailWord_3927263).sum := by decide
  have hdescent : baseEnd_3927263 < baseStart_3927263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927274 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 2, 5]
def baseStart_3927274 : Nat := 118140960795 + 3927274 * 2 ^ 59
def prefixEnd_3927274 : Nat := 4983230072969 + 3 ^ 40 * 3927274 * 2
def baseEnd_3927274 : Nat := 1344386149270381837409201

theorem tailTrace_3927274 : CollatzResearch.WordTrace tailWord_3927274 prefixEnd_3927274 1344386149270381837409201 := by
  unfold tailWord_3927274
  simp only [CollatzResearch.WordTrace]
  refine ⟨35809862593541124461291219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95492966916109665230109917 35809862593541124461291219)
  ·
    refine ⟨53714793890311686691936829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35809862593541124461291219 53714793890311686691936829)
    ·
      refine ⟨20143047708866882509476311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53714793890311686691936829 20143047708866882509476311)
      ·
        refine ⟨30214571563300323764214467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20143047708866882509476311 30214571563300323764214467)
        ·
          refine ⟨45321857344950485646321701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30214571563300323764214467 45321857344950485646321701)
          ·
            refine ⟨8497848252178216058685319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45321857344950485646321701 8497848252178216058685319)
            ·
              refine ⟨12746772378267324088027979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8497848252178216058685319 12746772378267324088027979)
              ·
                refine ⟨19120158567400986132041969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12746772378267324088027979 19120158567400986132041969)
                ·
                  refine ⟨14340118925550739599031477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19120158567400986132041969 14340118925550739599031477)
                  ·
                    refine ⟨1344386149270381837409201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14340118925550739599031477 1344386149270381837409201)
                    ·
                      rfl

theorem cell22_3927274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_3927274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927274 prefixEnd_3927274 := by exact prefixLift 3927274
  have htrace : WordTrace (prefixWord ++ tailWord_3927274) baseStart_3927274 baseEnd_3927274 := by
    simpa [prefixWord, tailWord_3927274, baseEnd_3927274] using wordTrace_append hprefix tailTrace_3927274
  have hstable : (prefixWord ++ tailWord_3927274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927274).length < 2 ^ (prefixWord ++ tailWord_3927274).sum := by decide
  have hdescent : baseEnd_3927274 < baseStart_3927274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927287 : List Nat := [1, 1, 3, 1, 1, 1, 2, 6, 6]
def baseStart_3927287 : Nat := 118140960795 + 3927287 * 2 ^ 59
def prefixEnd_3927287 : Nat := 4983230072969 + 3 ^ 40 * 3927287 * 2
def baseEnd_3927287 : Nat := 448130199812018045611387

theorem tailTrace_3927287 : CollatzResearch.WordTrace tailWord_3927287 prefixEnd_3927287 448130199812018045611387 := by
  unfold tailWord_3927287
  simp only [CollatzResearch.WordTrace]
  refine ⟨143239924523117401065388115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95493283015411600710258743 143239924523117401065388115)
  ·
    refine ⟨214859886784676101598082173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143239924523117401065388115 214859886784676101598082173)
    ·
      refine ⟨80572457544253538099280815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214859886784676101598082173 80572457544253538099280815)
      ·
        refine ⟨120858686316380307148921223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80572457544253538099280815 120858686316380307148921223)
        ·
          refine ⟨181288029474570460723381835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120858686316380307148921223 181288029474570460723381835)
          ·
            refine ⟨271932044211855691085072753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181288029474570460723381835 271932044211855691085072753)
            ·
              refine ⟨203949033158891768313804565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271932044211855691085072753 203949033158891768313804565)
              ·
                refine ⟨9560110929323051639709589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 203949033158891768313804565 9560110929323051639709589)
                ·
                  refine ⟨448130199812018045611387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9560110929323051639709589 448130199812018045611387)
                  ·
                    rfl

theorem cell22_3927287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 6].length) (baseStart_3927287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927287 prefixEnd_3927287 := by exact prefixLift 3927287
  have htrace : WordTrace (prefixWord ++ tailWord_3927287) baseStart_3927287 baseEnd_3927287 := by
    simpa [prefixWord, tailWord_3927287, baseEnd_3927287] using wordTrace_append hprefix tailTrace_3927287
  have hstable : (prefixWord ++ tailWord_3927287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927287).length < 2 ^ (prefixWord ++ tailWord_3927287).sum := by decide
  have hdescent : baseEnd_3927287 < baseStart_3927287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927289 : List Nat := [1, 2, 1, 3, 1, 1, 4, 4, 1, 4]
def baseStart_3927289 : Nat := 118140960795 + 3927289 * 2 ^ 59
def prefixEnd_3927289 : Nat := 4983230072969 + 3 ^ 40 * 3927289 * 2
def baseEnd_3927289 : Nat := 1344391284076926798284155

theorem tailTrace_3927289 : CollatzResearch.WordTrace tailWord_3927289 prefixEnd_3927289 1344391284076926798284155 := by
  unfold tailWord_3927289
  simp only [CollatzResearch.WordTrace]
  refine ⟨143239997469110155406960921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95493331646073436937973947 143239997469110155406960921)
  ·
    refine ⟨107429998101832616555220691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143239997469110155406960921 107429998101832616555220691)
    ·
      refine ⟨161144997152748924832831037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107429998101832616555220691 161144997152748924832831037)
      ·
        refine ⟨60429373932280846812311639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161144997152748924832831037 60429373932280846812311639)
        ·
          refine ⟨90644060898421270218467459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60429373932280846812311639 90644060898421270218467459)
          ·
            refine ⟨135966091347631905327701189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90644060898421270218467459 135966091347631905327701189)
            ·
              refine ⟨25493642127680982248943973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135966091347631905327701189 25493642127680982248943973)
              ·
                refine ⟨4780057898940184171676995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25493642127680982248943973 4780057898940184171676995)
                ·
                  refine ⟨7170086848410276257515493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4780057898940184171676995 7170086848410276257515493)
                  ·
                    refine ⟨1344391284076926798284155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7170086848410276257515493 1344391284076926798284155)
                    ·
                      rfl

theorem cell22_3927289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 4].length) (baseStart_3927289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927289 prefixEnd_3927289 := by exact prefixLift 3927289
  have htrace : WordTrace (prefixWord ++ tailWord_3927289) baseStart_3927289 baseEnd_3927289 := by
    simpa [prefixWord, tailWord_3927289, baseEnd_3927289] using wordTrace_append hprefix tailTrace_3927289
  have hstable : (prefixWord ++ tailWord_3927289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927289).length < 2 ^ (prefixWord ++ tailWord_3927289).sum := by decide
  have hdescent : baseEnd_3927289 < baseStart_3927289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927336 : List Nat := [2, 1, 5, 1, 2, 1, 3, 1, 1, 5]
def baseStart_3927336 : Nat := 118140960795 + 3927336 * 2 ^ 59
def prefixEnd_3927336 : Nat := 4983230072969 + 3 ^ 40 * 3927336 * 2
def baseEnd_3927336 : Nat := 1344407373137434342359011

theorem tailTrace_3927336 : CollatzResearch.WordTrace tailWord_3927336 prefixEnd_3927336 1344407373137434342359011 := by
  unfold tailWord_3927336
  simp only [CollatzResearch.WordTrace]
  refine ⟨71620855849969941216960931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95494474466626588289281241 71620855849969941216960931)
  ·
    refine ⟨107431283774954911825441397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71620855849969941216960931 107431283774954911825441397)
    ·
      refine ⟨10071682853902022983635131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107431283774954911825441397 10071682853902022983635131)
      ·
        refine ⟨15107524280853034475452697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10071682853902022983635131 15107524280853034475452697)
        ·
          refine ⟨11330643210639775856589523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15107524280853034475452697 11330643210639775856589523)
          ·
            refine ⟨16995964815959663784884285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11330643210639775856589523 16995964815959663784884285)
            ·
              refine ⟨6373486805984873919331607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16995964815959663784884285 6373486805984873919331607)
              ·
                refine ⟨9560230208977310878997411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6373486805984873919331607 9560230208977310878997411)
                ·
                  refine ⟨14340345313465966318496117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9560230208977310878997411 14340345313465966318496117)
                  ·
                    refine ⟨1344407373137434342359011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14340345313465966318496117 1344407373137434342359011)
                    ·
                      rfl

theorem cell22_3927336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_3927336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927336 prefixEnd_3927336 := by exact prefixLift 3927336
  have htrace : WordTrace (prefixWord ++ tailWord_3927336) baseStart_3927336 baseEnd_3927336 := by
    simpa [prefixWord, tailWord_3927336, baseEnd_3927336] using wordTrace_append hprefix tailTrace_3927336
  have hstable : (prefixWord ++ tailWord_3927336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927336).length < 2 ^ (prefixWord ++ tailWord_3927336).sum := by decide
  have hdescent : baseEnd_3927336 < baseStart_3927336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927349 : List Nat := [1, 3, 3, 1, 2, 3, 1, 8]
def baseStart_3927349 : Nat := 118140960795 + 3927349 * 2 ^ 59
def prefixEnd_3927349 : Nat := 4983230072969 + 3 ^ 40 * 3927349 * 2
def baseEnd_3927349 : Nat := 149379091478122960198219

theorem tailTrace_3927349 : CollatzResearch.WordTrace tailWord_3927349 prefixEnd_3927349 149379091478122960198219 := by
  unfold tailWord_3927349
  simp only [CollatzResearch.WordTrace]
  refine ⟨143242185848892785654145101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95494790565928523769430067 143242185848892785654145101)
  ·
    refine ⟨53715819693334794620304413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143242185848892785654145101 53715819693334794620304413)
    ·
      refine ⟨20143432385000547982614155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53715819693334794620304413 20143432385000547982614155)
      ·
        refine ⟨30215148577500821973921233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20143432385000547982614155 30215148577500821973921233)
        ·
          refine ⟨22661361433125616480440925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30215148577500821973921233 22661361433125616480440925)
          ·
            refine ⟨8498010537422106180165347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22661361433125616480440925 8498010537422106180165347)
            ·
              refine ⟨12747015806133159270248021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8498010537422106180165347 12747015806133159270248021)
              ·
                refine ⟨149379091478122960198219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12747015806133159270248021 149379091478122960198219)
                ·
                  rfl

theorem cell22_3927349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 8].length) (baseStart_3927349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927349 prefixEnd_3927349 := by exact prefixLift 3927349
  have htrace : WordTrace (prefixWord ++ tailWord_3927349) baseStart_3927349 baseEnd_3927349 := by
    simpa [prefixWord, tailWord_3927349, baseEnd_3927349] using wordTrace_append hprefix tailTrace_3927349
  have hstable : (prefixWord ++ tailWord_3927349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927349).length < 2 ^ (prefixWord ++ tailWord_3927349).sum := by decide
  have hdescent : baseEnd_3927349 < baseStart_3927349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927432 : List Nat := [2, 1, 3, 3, 1, 4, 2, 2, 1, 3]
def baseStart_3927432 : Nat := 118140960795 + 3927432 * 2 ^ 59
def prefixEnd_3927432 : Nat := 4983230072969 + 3 ^ 40 * 3927432 * 2
def baseEnd_3927432 : Nat := 1344440235899322091958717

theorem tailTrace_3927432 : CollatzResearch.WordTrace tailWord_3927432 prefixEnd_3927432 1344440235899322091958717 := by
  unfold tailWord_3927432
  simp only [CollatzResearch.WordTrace]
  refine ⟨71622606553796045414708275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95496808738394727219611033 71622606553796045414708275)
  ·
    refine ⟨107433909830694068122062413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71622606553796045414708275 107433909830694068122062413)
    ·
      refine ⟨40287716186510275545773405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107433909830694068122062413 40287716186510275545773405)
      ·
        refine ⟨15107893569941353329665027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40287716186510275545773405 15107893569941353329665027)
        ·
          refine ⟨22661840354912029994497541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15107893569941353329665027 22661840354912029994497541)
          ·
            refine ⟨4249095066546005623968289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22661840354912029994497541 4249095066546005623968289)
            ·
              refine ⟨3186821299909504217976217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4249095066546005623968289 3186821299909504217976217)
              ·
                refine ⟨2390115974932128163482163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3186821299909504217976217 2390115974932128163482163)
                ·
                  refine ⟨3585173962398192245223245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2390115974932128163482163 3585173962398192245223245)
                  ·
                    refine ⟨1344440235899322091958717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3585173962398192245223245 1344440235899322091958717)
                    ·
                      rfl

theorem cell22_3927432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_3927432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927432 prefixEnd_3927432 := by exact prefixLift 3927432
  have htrace : WordTrace (prefixWord ++ tailWord_3927432) baseStart_3927432 baseEnd_3927432 := by
    simpa [prefixWord, tailWord_3927432, baseEnd_3927432] using wordTrace_append hprefix tailTrace_3927432
  have hstable : (prefixWord ++ tailWord_3927432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927432).length < 2 ^ (prefixWord ++ tailWord_3927432).sum := by decide
  have hdescent : baseEnd_3927432 < baseStart_3927432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927473 : List Nat := [1, 2, 2, 4, 1, 1, 4, 3, 4]
def baseStart_3927473 : Nat := 118140960795 + 3927473 * 2 ^ 59
def prefixEnd_3927473 : Nat := 4983230072969 + 3 ^ 40 * 3927473 * 2
def baseEnd_3927473 : Nat := 448151423679070550561197

theorem tailTrace_3927473 : CollatzResearch.WordTrace tailWord_3927473 prefixEnd_3927473 448151423679070550561197 := by
  unfold tailWord_3927473
  simp only [CollatzResearch.WordTrace]
  refine ⟨143246708500443554831659073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95497805666962369887772715 143246708500443554831659073)
  ·
    refine ⟨107435031375332666123744305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143246708500443554831659073 107435031375332666123744305)
    ·
      refine ⟨80576273531499499592808229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107435031375332666123744305 80576273531499499592808229)
      ·
        refine ⟨15108051287156156173651543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80576273531499499592808229 15108051287156156173651543)
        ·
          refine ⟨22662076930734234260477315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15108051287156156173651543 22662076930734234260477315)
          ·
            refine ⟨33993115396101351390715973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22662076930734234260477315 33993115396101351390715973)
            ·
              refine ⟨6373709136769003385759245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33993115396101351390715973 6373709136769003385759245)
              ·
                refine ⟨2390140926288376269659717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6373709136769003385759245 2390140926288376269659717)
                ·
                  refine ⟨448151423679070550561197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2390140926288376269659717 448151423679070550561197)
                  ·
                    rfl

theorem cell22_3927473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 4].length) (baseStart_3927473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927473 prefixEnd_3927473 := by exact prefixLift 3927473
  have htrace : WordTrace (prefixWord ++ tailWord_3927473) baseStart_3927473 baseEnd_3927473 := by
    simpa [prefixWord, tailWord_3927473, baseEnd_3927473] using wordTrace_append hprefix tailTrace_3927473
  have hstable : (prefixWord ++ tailWord_3927473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927473).length < 2 ^ (prefixWord ++ tailWord_3927473).sum := by decide
  have hdescent : baseEnd_3927473 < baseStart_3927473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927486 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_3927486 : Nat := 118140960795 + 3927486 * 2 ^ 59
def prefixEnd_3927486 : Nat := 4983230072969 + 3 ^ 40 * 3927486 * 2
def baseEnd_3927486 : Nat := 1344458721202883951108551

theorem tailTrace_3927486 : CollatzResearch.WordTrace tailWord_3927486 prefixEnd_3927486 1344458721202883951108551 := by
  unfold tailWord_3927486
  simp only [CollatzResearch.WordTrace]
  refine ⟨17905897831174557256485289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95498121766264305367921541 17905897831174557256485289)
  ·
    refine ⟨13429423373380917942363967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17905897831174557256485289 13429423373380917942363967)
    ·
      refine ⟨20144135060071376913545951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13429423373380917942363967 20144135060071376913545951)
      ·
        refine ⟨30216202590107065370318927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20144135060071376913545951 30216202590107065370318927)
        ·
          refine ⟨45324303885160598055478391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30216202590107065370318927 45324303885160598055478391)
          ·
            refine ⟨67986455827740897083217587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45324303885160598055478391 67986455827740897083217587)
            ·
              refine ⟨101979683741611345624826381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67986455827740897083217587 101979683741611345624826381)
              ·
                refine ⟨38242381403104254609309893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101979683741611345624826381 38242381403104254609309893)
                ·
                  refine ⟨7170446513082047739245605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38242381403104254609309893 7170446513082047739245605)
                  ·
                    refine ⟨1344458721202883951108551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7170446513082047739245605 1344458721202883951108551)
                    ·
                      rfl

theorem cell22_3927486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_3927486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927486 prefixEnd_3927486 := by exact prefixLift 3927486
  have htrace : WordTrace (prefixWord ++ tailWord_3927486) baseStart_3927486 baseEnd_3927486 := by
    simpa [prefixWord, tailWord_3927486, baseEnd_3927486] using wordTrace_append hprefix tailTrace_3927486
  have hstable : (prefixWord ++ tailWord_3927486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927486).length < 2 ^ (prefixWord ++ tailWord_3927486).sum := by decide
  have hdescent : baseEnd_3927486 < baseStart_3927486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927488 : List Nat := [2, 1, 1, 2, 3, 1, 5, 2, 2, 3]
def baseStart_3927488 : Nat := 118140960795 + 3927488 * 2 ^ 59
def prefixEnd_3927488 : Nat := 4983230072969 + 3 ^ 40 * 3927488 * 2
def baseEnd_3927488 : Nat := 1344459405843756612558545

theorem tailTrace_3927488 : CollatzResearch.WordTrace tailWord_3927488 prefixEnd_3927488 1344459405843756612558545 := by
  unfold tailWord_3927488
  simp only [CollatzResearch.WordTrace]
  refine ⟨71623627797694606196727559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95498170396926141595636745 71623627797694606196727559)
  ·
    refine ⟨107435441696541909295091339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71623627797694606196727559 107435441696541909295091339)
    ·
      refine ⟨161153162544812863942637009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107435441696541909295091339 161153162544812863942637009)
      ·
        refine ⟨120864871908609647956977757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161153162544812863942637009 120864871908609647956977757)
        ·
          refine ⟨45324326965728617983866659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120864871908609647956977757 45324326965728617983866659)
          ·
            refine ⟨67986490448592926975799989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45324326965728617983866659 67986490448592926975799989)
            ·
              refine ⟨6373733479555586903981249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67986490448592926975799989 6373733479555586903981249)
              ·
                refine ⟨4780300109666690177985937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6373733479555586903981249 4780300109666690177985937)
                ·
                  refine ⟨3585225082250017633489453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4780300109666690177985937 3585225082250017633489453)
                  ·
                    refine ⟨1344459405843756612558545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3585225082250017633489453 1344459405843756612558545)
                    ·
                      rfl

theorem cell22_3927488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 2, 3].length) (baseStart_3927488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927488 prefixEnd_3927488 := by exact prefixLift 3927488
  have htrace : WordTrace (prefixWord ++ tailWord_3927488) baseStart_3927488 baseEnd_3927488 := by
    simpa [prefixWord, tailWord_3927488, baseEnd_3927488] using wordTrace_append hprefix tailTrace_3927488
  have hstable : (prefixWord ++ tailWord_3927488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927488).length < 2 ^ (prefixWord ++ tailWord_3927488).sum := by decide
  have hdescent : baseEnd_3927488 < baseStart_3927488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927546 : List Nat := [3, 1, 1, 1, 1, 2, 4, 4, 5]
def baseStart_3927546 : Nat := 118140960795 + 3927546 * 2 ^ 59
def prefixEnd_3927546 : Nat := 4983230072969 + 3 ^ 40 * 3927546 * 2
def baseEnd_3927546 : Nat := 448159753476354598202789

theorem tailTrace_3927546 : CollatzResearch.WordTrace tailWord_3927546 prefixEnd_3927546 448159753476354598202789 := by
  unfold tailWord_3927546
  simp only [CollatzResearch.WordTrace]
  refine ⟨35812342757294772074766623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95499580686119392199377661 35812342757294772074766623)
  ·
    refine ⟨53718514135942158112149935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35812342757294772074766623 53718514135942158112149935)
    ·
      refine ⟨80577771203913237168224903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53718514135942158112149935 80577771203913237168224903)
      ·
        refine ⟨120866656805869855752337355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80577771203913237168224903 120866656805869855752337355)
        ·
          refine ⟨181299985208804783628506033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120866656805869855752337355 181299985208804783628506033)
          ·
            refine ⟨135974988906603587721379525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181299985208804783628506033 135974988906603587721379525)
            ·
              refine ⟨25495310419988172697758661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135974988906603587721379525 25495310419988172697758661)
              ·
                refine ⟨4780370703747782380829749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25495310419988172697758661 4780370703747782380829749)
                ·
                  refine ⟨448159753476354598202789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4780370703747782380829749 448159753476354598202789)
                  ·
                    rfl

theorem cell22_3927546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_3927546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927546 prefixEnd_3927546 := by exact prefixLift 3927546
  have htrace : WordTrace (prefixWord ++ tailWord_3927546) baseStart_3927546 baseEnd_3927546 := by
    simpa [prefixWord, tailWord_3927546, baseEnd_3927546] using wordTrace_append hprefix tailTrace_3927546
  have hstable : (prefixWord ++ tailWord_3927546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927546).length < 2 ^ (prefixWord ++ tailWord_3927546).sum := by decide
  have hdescent : baseEnd_3927546 < baseStart_3927546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927563 : List Nat := [1, 1, 1, 1, 8, 1, 1, 3, 5]
def baseStart_3927563 : Nat := 118140960795 + 3927563 * 2 ^ 59
def prefixEnd_3927563 : Nat := 4983230072969 + 3 ^ 40 * 3927563 * 2
def baseEnd_3927563 : Nat := 448161693292160472311105

theorem tailTrace_3927563 : CollatzResearch.WordTrace tailWord_3927563 prefixEnd_3927563 448161693292160472311105 := by
  unfold tailWord_3927563
  simp only [CollatzResearch.WordTrace]
  refine ⟨143249991070117500202435343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95499994046745000134956895 143249991070117500202435343)
  ·
    refine ⟨214874986605176250303653015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143249991070117500202435343 214874986605176250303653015)
    ·
      refine ⟨322312479907764375455479523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214874986605176250303653015 322312479907764375455479523)
      ·
        refine ⟨483468719861646563183219285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322312479907764375455479523 483468719861646563183219285)
        ·
          refine ⟨5665649060878670662303351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 483468719861646563183219285 5665649060878670662303351)
          ·
            refine ⟨8498473591318005993455027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5665649060878670662303351 8498473591318005993455027)
            ·
              refine ⟨12747710386977008990182541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8498473591318005993455027 12747710386977008990182541)
              ·
                refine ⟨4780391395116378371318453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12747710386977008990182541 4780391395116378371318453)
                ·
                  refine ⟨448161693292160472311105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4780391395116378371318453 448161693292160472311105)
                  ·
                    rfl

theorem cell22_3927563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 5].length) (baseStart_3927563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927563 prefixEnd_3927563 := by exact prefixLift 3927563
  have htrace : WordTrace (prefixWord ++ tailWord_3927563) baseStart_3927563 baseEnd_3927563 := by
    simpa [prefixWord, tailWord_3927563, baseEnd_3927563] using wordTrace_append hprefix tailTrace_3927563
  have hstable : (prefixWord ++ tailWord_3927563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927563).length < 2 ^ (prefixWord ++ tailWord_3927563).sum := by decide
  have hdescent : baseEnd_3927563 < baseStart_3927563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927621 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 1, 6]
def baseStart_3927621 : Nat := 118140960795 + 3927621 * 2 ^ 59
def prefixEnd_3927621 : Nat := 4983230072969 + 3 ^ 40 * 3927621 * 2
def baseEnd_3927621 : Nat := 1344504934461788598983137

theorem tailTrace_3927621 : CollatzResearch.WordTrace tailWord_3927621 prefixEnd_3927621 1344504934461788598983137 := by
  unfold tailWord_3927621
  simp only [CollatzResearch.WordTrace]
  refine ⟨143252106503907376108046717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95501404335938250738697811 143252106503907376108046717)
  ·
    refine ⟨53719539938965266040517519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143252106503907376108046717 53719539938965266040517519)
    ·
      refine ⟨80579309908447899060776279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53719539938965266040517519 80579309908447899060776279)
      ·
        refine ⟨120868964862671848591164419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80579309908447899060776279 120868964862671848591164419)
        ·
          refine ⟨181303447294007772886746629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120868964862671848591164419 181303447294007772886746629)
          ·
            refine ⟨33994396367626457416264993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181303447294007772886746629 33994396367626457416264993)
            ·
              refine ⟨25495797275719843062198745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33994396367626457416264993 25495797275719843062198745)
              ·
                refine ⟨19121847956789882296649059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25495797275719843062198745 19121847956789882296649059)
                ·
                  refine ⟨28682771935184823444973589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19121847956789882296649059 28682771935184823444973589)
                  ·
                    refine ⟨1344504934461788598983137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28682771935184823444973589 1344504934461788598983137)
                    ·
                      rfl

theorem cell22_3927621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_3927621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927621 prefixEnd_3927621 := by exact prefixLift 3927621
  have htrace : WordTrace (prefixWord ++ tailWord_3927621) baseStart_3927621 baseEnd_3927621 := by
    simpa [prefixWord, tailWord_3927621, baseEnd_3927621] using wordTrace_append hprefix tailTrace_3927621
  have hstable : (prefixWord ++ tailWord_3927621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927621).length < 2 ^ (prefixWord ++ tailWord_3927621).sum := by decide
  have hdescent : baseEnd_3927621 < baseStart_3927621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927696 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 1, 7]
def baseStart_3927696 : Nat := 118140960795 + 3927696 * 2 ^ 59
def prefixEnd_3927696 : Nat := 4983230072969 + 3 ^ 40 * 3927696 * 2
def baseEnd_3927696 : Nat := 1344530608494513403357907

theorem tailTrace_3927696 : CollatzResearch.WordTrace tailWord_3927696 prefixEnd_3927696 1344530608494513403357907 := by
  unfold tailWord_3927696
  simp only [CollatzResearch.WordTrace]
  refine ⟨71627420989317831958513471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95503227985757109278017961 71627420989317831958513471)
  ·
    refine ⟨107441131483976747937770207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71627420989317831958513471 107441131483976747937770207)
    ·
      refine ⟨161161697225965121906655311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107441131483976747937770207 161161697225965121906655311)
      ·
        refine ⟨241742545838947682859982967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161161697225965121906655311 241742545838947682859982967)
        ·
          refine ⟨362613818758421524289974451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241742545838947682859982967 362613818758421524289974451)
          ·
            refine ⟨543920728137632286434961677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362613818758421524289974451 543920728137632286434961677)
            ·
              refine ⟨203970273051612107413110629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 543920728137632286434961677 203970273051612107413110629)
              ·
                refine ⟨38244426197177270139958243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203970273051612107413110629 38244426197177270139958243)
                ·
                  refine ⟨57366639295765905209937365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38244426197177270139958243 57366639295765905209937365)
                  ·
                    refine ⟨1344530608494513403357907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57366639295765905209937365 1344530608494513403357907)
                    ·
                      rfl

theorem cell22_3927696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_3927696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927696 prefixEnd_3927696 := by exact prefixLift 3927696
  have htrace : WordTrace (prefixWord ++ tailWord_3927696) baseStart_3927696 baseEnd_3927696 := by
    simpa [prefixWord, tailWord_3927696, baseEnd_3927696] using wordTrace_append hprefix tailTrace_3927696
  have hstable : (prefixWord ++ tailWord_3927696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927696).length < 2 ^ (prefixWord ++ tailWord_3927696).sum := by decide
  have hdescent : baseEnd_3927696 < baseStart_3927696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927777 : List Nat := [1, 2, 3, 1, 5, 1, 1, 4, 4]
def baseStart_3927777 : Nat := 118140960795 + 3927777 * 2 ^ 59
def prefixEnd_3927777 : Nat := 4983230072969 + 3 ^ 40 * 3927777 * 2
def baseEnd_3927777 : Nat := 448186112149952064027553

theorem tailTrace_3927777 : CollatzResearch.WordTrace tailWord_3927777 prefixEnd_3927777 448186112149952064027553 := by
  unfold tailWord_3927777
  simp only [CollatzResearch.WordTrace]
  refine ⟨143257796291342214750725585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95505197527561476500483723 143257796291342214750725585)
  ·
    refine ⟨107443347218506661063044189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143257796291342214750725585 107443347218506661063044189)
    ·
      refine ⟨40291255206939997898641571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107443347218506661063044189 40291255206939997898641571)
      ·
        refine ⟨60436882810409996847962357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40291255206939997898641571 60436882810409996847962357)
        ·
          refine ⟨5665957763475937204496471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60436882810409996847962357 5665957763475937204496471)
          ·
            refine ⟨8498936645213905806744707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5665957763475937204496471 8498936645213905806744707)
            ·
              refine ⟨12748404967820858710117061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8498936645213905806744707 12748404967820858710117061)
              ·
                refine ⟨2390325931466411008146949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12748404967820858710117061 2390325931466411008146949)
                ·
                  refine ⟨448186112149952064027553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2390325931466411008146949 448186112149952064027553)
                  ·
                    rfl

theorem cell22_3927777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 4].length) (baseStart_3927777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927777 prefixEnd_3927777 := by exact prefixLift 3927777
  have htrace : WordTrace (prefixWord ++ tailWord_3927777) baseStart_3927777 baseEnd_3927777 := by
    simpa [prefixWord, tailWord_3927777, baseEnd_3927777] using wordTrace_append hprefix tailTrace_3927777
  have hstable : (prefixWord ++ tailWord_3927777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927777).length < 2 ^ (prefixWord ++ tailWord_3927777).sum := by decide
  have hdescent : baseEnd_3927777 < baseStart_3927777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927788 : List Nat := [2, 2, 1, 1, 2, 2, 5, 7]
def baseStart_3927788 : Nat := 118140960795 + 3927788 * 2 ^ 59
def prefixEnd_3927788 : Nat := 4983230072969 + 3 ^ 40 * 3927788 * 2
def baseEnd_3927788 : Nat := 149395789108295092228625

theorem tailTrace_3927788 : CollatzResearch.WordTrace tailWord_3927788 prefixEnd_3927788 149395789108295092228625 := by
  unfold tailWord_3927788
  simp only [CollatzResearch.WordTrace]
  refine ⟨71629098747151181814688009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95505464996201575752917345 71629098747151181814688009)
  ·
    refine ⟨53721824060363386361016007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71629098747151181814688009 53721824060363386361016007)
    ·
      refine ⟨80582736090545079541524011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53721824060363386361016007 80582736090545079541524011)
      ·
        refine ⟨120874104135817619312286017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80582736090545079541524011 120874104135817619312286017)
        ·
          refine ⟨90655578101863214484214513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120874104135817619312286017 90655578101863214484214513)
          ·
            refine ⟨67991683576397410863160885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90655578101863214484214513 67991683576397410863160885)
            ·
              refine ⟨6374220335287257268421333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67991683576397410863160885 6374220335287257268421333)
              ·
                refine ⟨149395789108295092228625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6374220335287257268421333 149395789108295092228625)
                ·
                  rfl

theorem cell22_3927788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 7].length) (baseStart_3927788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927788 prefixEnd_3927788 := by exact prefixLift 3927788
  have htrace : WordTrace (prefixWord ++ tailWord_3927788) baseStart_3927788 baseEnd_3927788 := by
    simpa [prefixWord, tailWord_3927788, baseEnd_3927788] using wordTrace_append hprefix tailTrace_3927788
  have hstable : (prefixWord ++ tailWord_3927788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927788).length < 2 ^ (prefixWord ++ tailWord_3927788).sum := by decide
  have hdescent : baseEnd_3927788 < baseStart_3927788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927826 : List Nat := [3, 2, 4, 1, 1, 3, 1, 2, 2, 3]
def baseStart_3927826 : Nat := 118140960795 + 3927826 * 2 ^ 59
def prefixEnd_3927826 : Nat := 4983230072969 + 3 ^ 40 * 3927826 * 2
def baseEnd_3927826 : Nat := 1344575110151236397607509

theorem tailTrace_3927826 : CollatzResearch.WordTrace tailWord_3927826 prefixEnd_3927826 1344575110151236397607509 := by
  unfold tailWord_3927826
  simp only [CollatzResearch.WordTrace]
  refine ⟨35814895867041174029814833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95506388978776464079506221 35814895867041174029814833)
  ·
    refine ⟨26861171900280880522361125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35814895867041174029814833 26861171900280880522361125)
    ·
      refine ⟨5036469731302665097942711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26861171900280880522361125 5036469731302665097942711)
      ·
        refine ⟨7554704596953997646914067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5036469731302665097942711 7554704596953997646914067)
        ·
          refine ⟨11332056895430996470371101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7554704596953997646914067 11332056895430996470371101)
          ·
            refine ⟨4249521335786623676389163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11332056895430996470371101 4249521335786623676389163)
            ·
              refine ⟨6374282003679935514583745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4249521335786623676389163 6374282003679935514583745)
              ·
                refine ⟨4780711502759951635937809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6374282003679935514583745 4780711502759951635937809)
                ·
                  refine ⟨3585533627069963726953357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4780711502759951635937809 3585533627069963726953357)
                  ·
                    refine ⟨1344575110151236397607509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3585533627069963726953357 1344575110151236397607509)
                    ·
                      rfl

theorem cell22_3927826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_3927826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927826 prefixEnd_3927826 := by exact prefixLift 3927826
  have htrace : WordTrace (prefixWord ++ tailWord_3927826) baseStart_3927826 baseEnd_3927826 := by
    simpa [prefixWord, tailWord_3927826, baseEnd_3927826] using wordTrace_append hprefix tailTrace_3927826
  have hstable : (prefixWord ++ tailWord_3927826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927826).length < 2 ^ (prefixWord ++ tailWord_3927826).sum := by decide
  have hdescent : baseEnd_3927826 < baseStart_3927826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927871 : List Nat := [1, 1, 2, 2, 6, 2, 1, 3, 1, 3]
def baseStart_3927871 : Nat := 118140960795 + 3927871 * 2 ^ 59
def prefixEnd_3927871 : Nat := 4983230072969 + 3 ^ 40 * 3927871 * 2
def baseEnd_3927871 : Nat := 1344590514570871280232371

theorem tailTrace_3927871 : CollatzResearch.WordTrace tailWord_3927871 prefixEnd_3927871 1344590514570871280232371 := by
  unfold tailWord_3927871
  simp only [CollatzResearch.WordTrace]
  refine ⟨143261224753001668804647467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95507483168667779203098311 143261224753001668804647467)
  ·
    refine ⟨214891837129502503206971201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143261224753001668804647467 214891837129502503206971201)
    ·
      refine ⟨161168877847126877405228401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214891837129502503206971201 161168877847126877405228401)
      ·
        refine ⟨120876658385345158053921301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161168877847126877405228401 120876658385345158053921301)
        ·
          refine ⟨5666093361813054283777561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120876658385345158053921301 5666093361813054283777561)
          ·
            refine ⟨4249570021359790712833171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5666093361813054283777561 4249570021359790712833171)
            ·
              refine ⟨6374355032039686069249757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4249570021359790712833171 6374355032039686069249757)
              ·
                refine ⟨2390383137014882275968659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6374355032039686069249757 2390383137014882275968659)
                ·
                  refine ⟨3585574705522323413952989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2390383137014882275968659 3585574705522323413952989)
                  ·
                    refine ⟨1344590514570871280232371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3585574705522323413952989 1344590514570871280232371)
                    ·
                      rfl

theorem cell22_3927871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 1, 3].length) (baseStart_3927871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927871 prefixEnd_3927871 := by exact prefixLift 3927871
  have htrace : WordTrace (prefixWord ++ tailWord_3927871) baseStart_3927871 baseEnd_3927871 := by
    simpa [prefixWord, tailWord_3927871, baseEnd_3927871] using wordTrace_append hprefix tailTrace_3927871
  have hstable : (prefixWord ++ tailWord_3927871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927871).length < 2 ^ (prefixWord ++ tailWord_3927871).sum := by decide
  have hdescent : baseEnd_3927871 < baseStart_3927871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927914 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 3, 4]
def baseStart_3927914 : Nat := 118140960795 + 3927914 * 2 ^ 59
def prefixEnd_3927914 : Nat := 4983230072969 + 3 ^ 40 * 3927914 * 2
def baseEnd_3927914 : Nat := 1344605234349633501407239

theorem tailTrace_3927914 : CollatzResearch.WordTrace tailWord_3927914 prefixEnd_3927914 1344605234349633501407239 := by
  unfold tailWord_3927914
  simp only [CollatzResearch.WordTrace]
  refine ⟨35815698272961471787115699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95508528727897258098975197 35815698272961471787115699)
  ·
    refine ⟨53723547409442207680673549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35815698272961471787115699 53723547409442207680673549)
    ·
      refine ⟨20146330278540827880252581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53723547409442207680673549 20146330278540827880252581)
      ·
        refine ⟨3777436927226405227547359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20146330278540827880252581 3777436927226405227547359)
        ·
          refine ⟨5666155390839607841321039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3777436927226405227547359 5666155390839607841321039)
          ·
            refine ⟨8499233086259411761981559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5666155390839607841321039 8499233086259411761981559)
            ·
              refine ⟨12748849629389117642972339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8499233086259411761981559 12748849629389117642972339)
              ·
                refine ⟨19123274444083676464458509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12748849629389117642972339 19123274444083676464458509)
                ·
                  refine ⟨7171227916531378674171941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19123274444083676464458509 7171227916531378674171941)
                  ·
                    refine ⟨1344605234349633501407239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7171227916531378674171941 1344605234349633501407239)
                    ·
                      rfl

theorem cell22_3927914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_3927914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927914 prefixEnd_3927914 := by exact prefixLift 3927914
  have htrace : WordTrace (prefixWord ++ tailWord_3927914) baseStart_3927914 baseEnd_3927914 := by
    simpa [prefixWord, tailWord_3927914, baseEnd_3927914] using wordTrace_append hprefix tailTrace_3927914
  have hstable : (prefixWord ++ tailWord_3927914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927914).length < 2 ^ (prefixWord ++ tailWord_3927914).sum := by decide
  have hdescent : baseEnd_3927914 < baseStart_3927914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927972 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 5, 3]
def baseStart_3927972 : Nat := 118140960795 + 3927972 * 2 ^ 59
def prefixEnd_3927972 : Nat := 4983230072969 + 3 ^ 40 * 3927972 * 2
def baseEnd_3927972 : Nat := 1344625088934940683457061

theorem tailTrace_3927972 : CollatzResearch.WordTrace tailWord_3927972 prefixEnd_3927972 1344625088934940683457061 := by
  unfold tailWord_3927972
  simp only [CollatzResearch.WordTrace]
  refine ⟨71632454262817881527037085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95509939017090508702716113 71632454262817881527037085)
  ·
    refine ⟨26862170348556705572638907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71632454262817881527037085 26862170348556705572638907)
    ·
      refine ⟨40293255522835058358958361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26862170348556705572638907 40293255522835058358958361)
      ·
        refine ⟨30219941642126293769218771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40293255522835058358958361 30219941642126293769218771)
        ·
          refine ⟨45329912463189440653828157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30219941642126293769218771 45329912463189440653828157)
          ·
            refine ⟨16998717173696040245185559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45329912463189440653828157 16998717173696040245185559)
            ·
              refine ⟨25498075760544060367778339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16998717173696040245185559 25498075760544060367778339)
              ·
                refine ⟨38247113640816090551667509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25498075760544060367778339 38247113640816090551667509)
                ·
                  refine ⟨3585666903826508489218829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38247113640816090551667509 3585666903826508489218829)
                  ·
                    refine ⟨1344625088934940683457061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3585666903826508489218829 1344625088934940683457061)
                    ·
                      rfl

theorem cell22_3927972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_3927972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927972 prefixEnd_3927972 := by exact prefixLift 3927972
  have htrace : WordTrace (prefixWord ++ tailWord_3927972) baseStart_3927972 baseEnd_3927972 := by
    simpa [prefixWord, tailWord_3927972, baseEnd_3927972] using wordTrace_append hprefix tailTrace_3927972
  have hstable : (prefixWord ++ tailWord_3927972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927972).length < 2 ^ (prefixWord ++ tailWord_3927972).sum := by decide
  have hdescent : baseEnd_3927972 < baseStart_3927972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927982 : List Nat := [4, 1, 5, 1, 2, 1, 2, 1, 1, 4]
def baseStart_3927982 : Nat := 118140960795 + 3927982 * 2 ^ 59
def prefixEnd_3927982 : Nat := 4983230072969 + 3 ^ 40 * 3927982 * 2
def baseEnd_3927982 : Nat := 1344628512139303990707031

theorem tailTrace_3927982 : CollatzResearch.WordTrace tailWord_3927982 prefixEnd_3927982 1344628512139303990707031 := by
  unfold tailWord_3927982
  simp only [CollatzResearch.WordTrace]
  refine ⟨17908159156949941845242275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95510182170399689841292133 17908159156949941845242275)
  ·
    refine ⟨26862238735424912767863413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17908159156949941845242275 26862238735424912767863413)
    ·
      refine ⟨2518334881446085571987195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26862238735424912767863413 2518334881446085571987195)
      ·
        refine ⟨3777502322169128357980793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2518334881446085571987195 3777502322169128357980793)
        ·
          refine ⟨2833126741626846268485595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3777502322169128357980793 2833126741626846268485595)
          ·
            refine ⟨4249690112440269402728393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2833126741626846268485595 4249690112440269402728393)
            ·
              refine ⟨3187267584330202052046295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4249690112440269402728393 3187267584330202052046295)
              ·
                refine ⟨4780901376495303078069443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3187267584330202052046295 4780901376495303078069443)
                ·
                  refine ⟨7171352064742954617104165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4780901376495303078069443 7171352064742954617104165)
                  ·
                    refine ⟨1344628512139303990707031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7171352064742954617104165 1344628512139303990707031)
                    ·
                      rfl

theorem cell22_3927982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_3927982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3927982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3927982 prefixEnd_3927982 := by exact prefixLift 3927982
  have htrace : WordTrace (prefixWord ++ tailWord_3927982) baseStart_3927982 baseEnd_3927982 := by
    simpa [prefixWord, tailWord_3927982, baseEnd_3927982] using wordTrace_append hprefix tailTrace_3927982
  have hstable : (prefixWord ++ tailWord_3927982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927982).length < 2 ^ (prefixWord ++ tailWord_3927982).sum := by decide
  have hdescent : baseEnd_3927982 < baseStart_3927982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928000 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 4, 5]
def baseStart_3928000 : Nat := 118140960795 + 3928000 * 2 ^ 59
def prefixEnd_3928000 : Nat := 4983230072969 + 3 ^ 40 * 3928000 * 2
def baseEnd_3928000 : Nat := 1344634673907157943756975

theorem tailTrace_3928000 : CollatzResearch.WordTrace tailWord_3928000 prefixEnd_3928000 1344634673907157943756975 := by
  unfold tailWord_3928000
  simp only [CollatzResearch.WordTrace]
  refine ⟨71632964884767161918046727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95510619846356215890728969 71632964884767161918046727)
  ·
    refine ⟨107449447327150742877070091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71632964884767161918046727 107449447327150742877070091)
    ·
      refine ⟨161174170990726114315605137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107449447327150742877070091 161174170990726114315605137)
      ·
        refine ⟨120880628243044585736703853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161174170990726114315605137 120880628243044585736703853)
        ·
          refine ⟨45330235591141719651263945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120880628243044585736703853 45330235591141719651263945)
          ·
            refine ⟨33997676693356289738447959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45330235591141719651263945 33997676693356289738447959)
            ·
              refine ⟨50996515040034434607671939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33997676693356289738447959 50996515040034434607671939)
              ·
                refine ⟨76494772560051651911507909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50996515040034434607671939 76494772560051651911507909)
                ·
                  refine ⟨14342769855009684733407733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76494772560051651911507909 14342769855009684733407733)
                  ·
                    refine ⟨1344634673907157943756975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14342769855009684733407733 1344634673907157943756975)
                    ·
                      rfl

theorem cell22_3928000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_3928000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928000 prefixEnd_3928000 := by exact prefixLift 3928000
  have htrace : WordTrace (prefixWord ++ tailWord_3928000) baseStart_3928000 baseEnd_3928000 := by
    simpa [prefixWord, tailWord_3928000, baseEnd_3928000] using wordTrace_append hprefix tailTrace_3928000
  have hstable : (prefixWord ++ tailWord_3928000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928000).length < 2 ^ (prefixWord ++ tailWord_3928000).sum := by decide
  have hdescent : baseEnd_3928000 < baseStart_3928000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928070 : List Nat := [6, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_3928070 : Nat := 118140960795 + 3928070 * 2 ^ 59
def prefixEnd_3928070 : Nat := 4983230072969 + 3 ^ 40 * 3928070 * 2
def baseEnd_3928070 : Nat := 448219545445900364835587

theorem tailTrace_3928070 : CollatzResearch.WordTrace tailWord_3928070 prefixEnd_3928070 448219545445900364835587 := by
  unfold tailWord_3928070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4477140089977522680973177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95512321919520483860761109 4477140089977522680973177)
  ·
    refine ⟨3357855067483142010729883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4477140089977522680973177 3357855067483142010729883)
    ·
      refine ⟨5036782601224713016094825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3357855067483142010729883 5036782601224713016094825)
      ·
        refine ⟨3777586950918534762071119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5036782601224713016094825 3777586950918534762071119)
        ·
          refine ⟨5666380426377802143106679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3777586950918534762071119 5666380426377802143106679)
          ·
            refine ⟨8499570639566703214660019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5666380426377802143106679 8499570639566703214660019)
            ·
              refine ⟨12749355959350054821990029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8499570639566703214660019 12749355959350054821990029)
              ·
                refine ⟨4781008484756270558246261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12749355959350054821990029 4781008484756270558246261)
                ·
                  refine ⟨448219545445900364835587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4781008484756270558246261 448219545445900364835587)
                  ·
                    rfl

theorem cell22_3928070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_3928070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928070 prefixEnd_3928070 := by exact prefixLift 3928070
  have htrace : WordTrace (prefixWord ++ tailWord_3928070) baseStart_3928070 baseEnd_3928070 := by
    simpa [prefixWord, tailWord_3928070, baseEnd_3928070] using wordTrace_append hprefix tailTrace_3928070
  have hstable : (prefixWord ++ tailWord_3928070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928070).length < 2 ^ (prefixWord ++ tailWord_3928070).sum := by decide
  have hdescent : baseEnd_3928070 < baseStart_3928070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928092 : List Nat := [2, 2, 3, 1, 3, 1, 2, 8]
def baseStart_3928092 : Nat := 118140960795 + 3928092 * 2 ^ 59
def prefixEnd_3928092 : Nat := 4983230072969 + 3 ^ 40 * 3928092 * 2
def baseEnd_3928092 : Nat := 149407351931922263384077

theorem tailTrace_3928092 : CollatzResearch.WordTrace tailWord_3928092 prefixEnd_3928092 149407351931922263384077 := by
  unfold tailWord_3928092
  simp only [CollatzResearch.WordTrace]
  refine ⟨71634642642600511774221265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95512856856800682365628353 71634642642600511774221265)
  ·
    refine ⟨53725981981950383830665949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71634642642600511774221265 53725981981950383830665949)
    ·
      refine ⟨20147243243231393936499731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53725981981950383830665949 20147243243231393936499731)
      ·
        refine ⟨30220864864847090904749597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20147243243231393936499731 30220864864847090904749597)
        ·
          refine ⟨11332824324317659089281099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30220864864847090904749597 11332824324317659089281099)
          ·
            refine ⟨16999236486476488633921649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11332824324317659089281099 16999236486476488633921649)
            ·
              refine ⟨12749427364857366475441237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16999236486476488633921649 12749427364857366475441237)
              ·
                refine ⟨149407351931922263384077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12749427364857366475441237 149407351931922263384077)
                ·
                  rfl

theorem cell22_3928092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 8].length) (baseStart_3928092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928092 prefixEnd_3928092 := by exact prefixLift 3928092
  have htrace : WordTrace (prefixWord ++ tailWord_3928092) baseStart_3928092 baseEnd_3928092 := by
    simpa [prefixWord, tailWord_3928092, baseEnd_3928092] using wordTrace_append hprefix tailTrace_3928092
  have hstable : (prefixWord ++ tailWord_3928092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928092).length < 2 ^ (prefixWord ++ tailWord_3928092).sum := by decide
  have hdescent : baseEnd_3928092 < baseStart_3928092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928107 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 7, 3]
def baseStart_3928107 : Nat := 118140960795 + 3928107 * 2 ^ 59
def prefixEnd_3928107 : Nat := 4983230072969 + 3 ^ 40 * 3928107 * 2
def baseEnd_3928107 : Nat := 1344671302193845331331647

theorem tailTrace_3928107 : CollatzResearch.WordTrace tailWord_3928107 prefixEnd_3928107 1344671302193845331331647 := by
  unfold tailWord_3928107
  simp only [CollatzResearch.WordTrace]
  refine ⟨143269832380146681110238575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95513221586764454073492383 143269832380146681110238575)
  ·
    refine ⟨214904748570220021665357863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143269832380146681110238575 214904748570220021665357863)
    ·
      refine ⟨322357122855330032498036795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214904748570220021665357863 322357122855330032498036795)
      ·
        refine ⟨483535684282995048747055193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322357122855330032498036795 483535684282995048747055193)
        ·
          refine ⟨362651763212246286560291395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483535684282995048747055193 362651763212246286560291395)
          ·
            refine ⟨543977644818369429840437093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362651763212246286560291395 543977644818369429840437093)
            ·
              refine ⟨101995808403444268095081955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 543977644818369429840437093 101995808403444268095081955)
              ·
                refine ⟨152993712605166402142622933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101995808403444268095081955 152993712605166402142622933)
                ·
                  refine ⟨3585790139183587550217725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 152993712605166402142622933 3585790139183587550217725)
                  ·
                    refine ⟨1344671302193845331331647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3585790139183587550217725 1344671302193845331331647)
                    ·
                      rfl

theorem cell22_3928107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 3].length) (baseStart_3928107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928107 prefixEnd_3928107 := by exact prefixLift 3928107
  have htrace : WordTrace (prefixWord ++ tailWord_3928107) baseStart_3928107 baseEnd_3928107 := by
    simpa [prefixWord, tailWord_3928107, baseEnd_3928107] using wordTrace_append hprefix tailTrace_3928107
  have hstable : (prefixWord ++ tailWord_3928107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928107).length < 2 ^ (prefixWord ++ tailWord_3928107).sum := by decide
  have hdescent : baseEnd_3928107 < baseStart_3928107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928124 : List Nat := [2, 2, 2, 2, 2, 1, 2, 3, 3, 3]
def baseStart_3928124 : Nat := 118140960795 + 3928124 * 2 ^ 59
def prefixEnd_3928124 : Nat := 4983230072969 + 3 ^ 40 * 3928124 * 2
def baseEnd_3928124 : Nat := 1344677121641262953656595

theorem tailTrace_3928124 : CollatzResearch.WordTrace tailWord_3928124 prefixEnd_3928124 1344677121641262953656595 := by
  unfold tailWord_3928124
  simp only [CollatzResearch.WordTrace]
  refine ⟨71635226210542546506803713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95513634947390062009071617 71635226210542546506803713)
  ·
    refine ⟨53726419657906909880102785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71635226210542546506803713 53726419657906909880102785)
    ·
      refine ⟨40294814743430182410077089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53726419657906909880102785 40294814743430182410077089)
      ·
        refine ⟨30221111057572636807557817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40294814743430182410077089 30221111057572636807557817)
        ·
          refine ⟨22665833293179477605668363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30221111057572636807557817 22665833293179477605668363)
          ·
            refine ⟨33998749939769216408502545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22665833293179477605668363 33998749939769216408502545)
            ·
              refine ⟨25499062454826912306376909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33998749939769216408502545 25499062454826912306376909)
              ·
                refine ⟨9562148420560092114891341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25499062454826912306376909 9562148420560092114891341)
                ·
                  refine ⟨3585805657710034543084253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9562148420560092114891341 3585805657710034543084253)
                  ·
                    refine ⟨1344677121641262953656595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3585805657710034543084253 1344677121641262953656595)
                    ·
                      rfl

theorem cell22_3928124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_3928124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928124 prefixEnd_3928124 := by exact prefixLift 3928124
  have htrace : WordTrace (prefixWord ++ tailWord_3928124) baseStart_3928124 baseEnd_3928124 := by
    simpa [prefixWord, tailWord_3928124, baseEnd_3928124] using wordTrace_append hprefix tailTrace_3928124
  have hstable : (prefixWord ++ tailWord_3928124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928124).length < 2 ^ (prefixWord ++ tailWord_3928124).sum := by decide
  have hdescent : baseEnd_3928124 < baseStart_3928124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928126 : List Nat := [4, 2, 1, 3, 2, 2, 1, 7]
def baseStart_3928126 : Nat := 118140960795 + 3928126 * 2 ^ 59
def prefixEnd_3928126 : Nat := 4983230072969 + 3 ^ 40 * 3928126 * 2
def baseEnd_3928126 : Nat := 149408645142459512789621

theorem tailTrace_3928126 : CollatzResearch.WordTrace tailWord_3928126 prefixEnd_3928126 149408645142459512789621 := by
  unfold tailWord_3928126
  simp only [CollatzResearch.WordTrace]
  refine ⟨17908815670884730919397529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95513683578051898236786821 17908815670884730919397529)
  ·
    refine ⟨13431611753163548189548147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17908815670884730919397529 13431611753163548189548147)
    ·
      refine ⟨20147417629745322284322221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13431611753163548189548147 20147417629745322284322221)
      ·
        refine ⟨7555281611154495856620833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20147417629745322284322221 7555281611154495856620833)
        ·
          refine ⟨5666461208365871892465625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7555281611154495856620833 5666461208365871892465625)
          ·
            refine ⟨4249845906274403919349219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5666461208365871892465625 4249845906274403919349219)
            ·
              refine ⟨6374768859411605879023829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4249845906274403919349219 6374768859411605879023829)
              ·
                refine ⟨149408645142459512789621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6374768859411605879023829 149408645142459512789621)
                ·
                  rfl

theorem cell22_3928126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_3928126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928126 prefixEnd_3928126 := by exact prefixLift 3928126
  have htrace : WordTrace (prefixWord ++ tailWord_3928126) baseStart_3928126 baseEnd_3928126 := by
    simpa [prefixWord, tailWord_3928126, baseEnd_3928126] using wordTrace_append hprefix tailTrace_3928126
  have hstable : (prefixWord ++ tailWord_3928126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928126).length < 2 ^ (prefixWord ++ tailWord_3928126).sum := by decide
  have hdescent : baseEnd_3928126 < baseStart_3928126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928137 : List Nat := [1, 2, 1, 1, 2, 2, 3, 5, 5]
def baseStart_3928137 : Nat := 118140960795 + 3928137 * 2 ^ 59
def prefixEnd_3928137 : Nat := 4983230072969 + 3 ^ 40 * 3928137 * 2
def baseEnd_3928137 : Nat := 448227190602311751027185

theorem tailTrace_3928137 : CollatzResearch.WordTrace tailWord_3928137 prefixEnd_3928137 448227190602311751027185 := by
  unfold tailWord_3928137
  simp only [CollatzResearch.WordTrace]
  refine ⟨143270926570037996233830665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95513951046691997489220443 143270926570037996233830665)
  ·
    refine ⟨107453194927528497175372999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143270926570037996233830665 107453194927528497175372999)
    ·
      refine ⟨161179792391292745763059499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107453194927528497175372999 161179792391292745763059499)
      ·
        refine ⟨241769688586939118644589249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161179792391292745763059499 241769688586939118644589249)
        ·
          refine ⟨181327266440204338983441937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241769688586939118644589249 181327266440204338983441937)
          ·
            refine ⟨135995449830153254237581453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181327266440204338983441937 135995449830153254237581453)
            ·
              refine ⟨50998293686307470339093045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135995449830153254237581453 50998293686307470339093045)
              ·
                refine ⟨4781090033091325344289973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50998293686307470339093045 4781090033091325344289973)
                ·
                  refine ⟨448227190602311751027185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4781090033091325344289973 448227190602311751027185)
                  ·
                    rfl

theorem cell22_3928137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 5].length) (baseStart_3928137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928137 prefixEnd_3928137 := by exact prefixLift 3928137
  have htrace : WordTrace (prefixWord ++ tailWord_3928137) baseStart_3928137 baseEnd_3928137 := by
    simpa [prefixWord, tailWord_3928137, baseEnd_3928137] using wordTrace_append hprefix tailTrace_3928137
  have hstable : (prefixWord ++ tailWord_3928137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928137).length < 2 ^ (prefixWord ++ tailWord_3928137).sum := by decide
  have hdescent : baseEnd_3928137 < baseStart_3928137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928141 : List Nat := [1, 6, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_3928141 : Nat := 118140960795 + 3928141 * 2 ^ 59
def prefixEnd_3928141 : Nat := 4983230072969 + 3 ^ 40 * 3928141 * 2
def baseEnd_3928141 : Nat := 1344682941088680575981543

theorem tailTrace_3928141 : CollatzResearch.WordTrace tailWord_3928141 prefixEnd_3928141 1344682941088680575981543 := by
  unfold tailWord_3928141
  simp only [CollatzResearch.WordTrace]
  refine ⟨143271072462023504916976277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95514048308015669944650851 143271072462023504916976277)
  ·
    refine ⟨6715831521657351792983263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143271072462023504916976277 6715831521657351792983263)
    ·
      refine ⟨10073747282486027689474895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6715831521657351792983263 10073747282486027689474895)
      ·
        refine ⟨15110620923729041534212343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10073747282486027689474895 15110620923729041534212343)
        ·
          refine ⟨22665931385593562301318515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15110620923729041534212343 22665931385593562301318515)
          ·
            refine ⟨33998897078390343451977773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22665931385593562301318515 33998897078390343451977773)
            ·
              refine ⟨12749586404396378794491665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33998897078390343451977773 12749586404396378794491665)
              ·
                refine ⟨9562189803297284095868749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12749586404396378794491665 9562189803297284095868749)
                ·
                  refine ⟨3585821176236481535950781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9562189803297284095868749 3585821176236481535950781)
                  ·
                    refine ⟨1344682941088680575981543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3585821176236481535950781 1344682941088680575981543)
                    ·
                      rfl

theorem cell22_3928141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_3928141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928141 prefixEnd_3928141 := by exact prefixLift 3928141
  have htrace : WordTrace (prefixWord ++ tailWord_3928141) baseStart_3928141 baseEnd_3928141 := by
    simpa [prefixWord, tailWord_3928141, baseEnd_3928141] using wordTrace_append hprefix tailTrace_3928141
  have hstable : (prefixWord ++ tailWord_3928141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928141).length < 2 ^ (prefixWord ++ tailWord_3928141).sum := by decide
  have hdescent : baseEnd_3928141 < baseStart_3928141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928229 : List Nat := [1, 3, 1, 2, 1, 3, 3, 2, 2, 4]
def baseStart_3928229 : Nat := 118140960795 + 3928229 * 2 ^ 59
def prefixEnd_3928229 : Nat := 4983230072969 + 3 ^ 40 * 3928229 * 2
def baseEnd_3928229 : Nat := 1344713065287077679781273

theorem tailTrace_3928229 : CollatzResearch.WordTrace tailWord_3928229 prefixEnd_3928229 1344713065287077679781273 := by
  unfold tailWord_3928229
  simp only [CollatzResearch.WordTrace]
  refine ⟨143274282085704695946179741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95516188057136463964119827 143274282085704695946179741)
  ·
    refine ⟨53727855782139260979817403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143274282085704695946179741 53727855782139260979817403)
    ·
      refine ⟨80591783673208891469726105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53727855782139260979817403 80591783673208891469726105)
      ·
        refine ⟨60443837754906668602294579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80591783673208891469726105 60443837754906668602294579)
        ·
          refine ⟨90665756632360002903441869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60443837754906668602294579 90665756632360002903441869)
          ·
            refine ⟨33999658737135001088790701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90665756632360002903441869 33999658737135001088790701)
            ·
              refine ⟨12749872026425625408296513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33999658737135001088790701 12749872026425625408296513)
              ·
                refine ⟨9562404019819219056222385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12749872026425625408296513 9562404019819219056222385)
                ·
                  refine ⟨7171803014864414292166789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9562404019819219056222385 7171803014864414292166789)
                  ·
                    refine ⟨1344713065287077679781273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7171803014864414292166789 1344713065287077679781273)
                    ·
                      rfl

theorem cell22_3928229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_3928229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928229 prefixEnd_3928229 := by exact prefixLift 3928229
  have htrace : WordTrace (prefixWord ++ tailWord_3928229) baseStart_3928229 baseEnd_3928229 := by
    simpa [prefixWord, tailWord_3928229, baseEnd_3928229] using wordTrace_append hprefix tailTrace_3928229
  have hstable : (prefixWord ++ tailWord_3928229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928229).length < 2 ^ (prefixWord ++ tailWord_3928229).sum := by decide
  have hdescent : baseEnd_3928229 < baseStart_3928229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928284 : List Nat := [2, 2, 5, 2, 2, 1, 2, 2, 4]
def baseStart_3928284 : Nat := 118140960795 + 3928284 * 2 ^ 59
def prefixEnd_3928284 : Nat := 4983230072969 + 3 ^ 40 * 3928284 * 2
def baseEnd_3928284 : Nat := 448243964303691956552035

theorem tailTrace_3928284 : CollatzResearch.WordTrace tailWord_3928284 prefixEnd_3928284 448243964303691956552035 := by
  unfold tailWord_3928284
  simp only [CollatzResearch.WordTrace]
  refine ⟨71638144050252720169715953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95517525400336960226287937 71638144050252720169715953)
  ·
    refine ⟨53728608037689540127286965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71638144050252720169715953 53728608037689540127286965)
    ·
      refine ⟨5037057003533394386933153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53728608037689540127286965 5037057003533394386933153)
      ·
        refine ⟨3777792752650045790199865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5037057003533394386933153 3777792752650045790199865)
        ·
          refine ⟨2833344564487534342649899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3777792752650045790199865 2833344564487534342649899)
          ·
            refine ⟨4250016846731301513974849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2833344564487534342649899 4250016846731301513974849)
            ·
              refine ⟨3187512635048476135481137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4250016846731301513974849 3187512635048476135481137)
              ·
                refine ⟨2390634476286357101610853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3187512635048476135481137 2390634476286357101610853)
                ·
                  refine ⟨448243964303691956552035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2390634476286357101610853 448243964303691956552035)
                  ·
                    rfl

theorem cell22_3928284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_3928284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928284 prefixEnd_3928284 := by exact prefixLift 3928284
  have htrace : WordTrace (prefixWord ++ tailWord_3928284) baseStart_3928284 baseEnd_3928284 := by
    simpa [prefixWord, tailWord_3928284, baseEnd_3928284] using wordTrace_append hprefix tailTrace_3928284
  have hstable : (prefixWord ++ tailWord_3928284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928284).length < 2 ^ (prefixWord ++ tailWord_3928284).sum := by decide
  have hdescent : baseEnd_3928284 < baseStart_3928284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928306 : List Nat := [3, 2, 1, 3, 2, 1, 2, 3, 5]
def baseStart_3928306 : Nat := 118140960795 + 3928306 * 2 ^ 59
def prefixEnd_3928306 : Nat := 4983230072969 + 3 ^ 40 * 3928306 * 2
def baseEnd_3928306 : Nat := 448246474653558381868679

theorem tailTrace_3928306 : CollatzResearch.WordTrace tailWord_3928306 prefixEnd_3928306 448246474653558381868679 := by
  unfold tailWord_3928306
  simp only [CollatzResearch.WordTrace]
  refine ⟨35819272626606434524183193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95518060337617158731155181 35819272626606434524183193)
  ·
    refine ⟨26864454469954825893137395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35819272626606434524183193 26864454469954825893137395)
    ·
      refine ⟨40296681704932238839706093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26864454469954825893137395 40296681704932238839706093)
      ·
        refine ⟨15111255639349589564889785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40296681704932238839706093 15111255639349589564889785)
        ·
          refine ⟨11333441729512192173667339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15111255639349589564889785 11333441729512192173667339)
          ·
            refine ⟨17000162594268288260501009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11333441729512192173667339 17000162594268288260501009)
            ·
              refine ⟨12750121945701216195375757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17000162594268288260501009 12750121945701216195375757)
              ·
                refine ⟨4781295729637956073265909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12750121945701216195375757 4781295729637956073265909)
                ·
                  refine ⟨448246474653558381868679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4781295729637956073265909 448246474653558381868679)
                  ·
                    rfl

theorem cell22_3928306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_3928306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928306 prefixEnd_3928306 := by exact prefixLift 3928306
  have htrace : WordTrace (prefixWord ++ tailWord_3928306) baseStart_3928306 baseEnd_3928306 := by
    simpa [prefixWord, tailWord_3928306, baseEnd_3928306] using wordTrace_append hprefix tailTrace_3928306
  have hstable : (prefixWord ++ tailWord_3928306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928306).length < 2 ^ (prefixWord ++ tailWord_3928306).sum := by decide
  have hdescent : baseEnd_3928306 < baseStart_3928306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928319 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 3, 4]
def baseStart_3928319 : Nat := 118140960795 + 3928319 * 2 ^ 59
def prefixEnd_3928319 : Nat := 4983230072969 + 3 ^ 40 * 3928319 * 2
def baseEnd_3928319 : Nat := 1344743874126347445030997

theorem tailTrace_3928319 : CollatzResearch.WordTrace tailWord_3928319 prefixEnd_3928319 1344743874126347445030997 := by
  unfold tailWord_3928319
  simp only [CollatzResearch.WordTrace]
  refine ⟨143277564655378641316956011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95518376436919094211304007 143277564655378641316956011)
  ·
    refine ⟨214916346983067961975434017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143277564655378641316956011 214916346983067961975434017)
    ·
      refine ⟨161187260237300971481575513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214916346983067961975434017 161187260237300971481575513)
      ·
        refine ⟨120890445177975728611181635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161187260237300971481575513 120890445177975728611181635)
        ·
          refine ⟨181335667766963592916772453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120890445177975728611181635 181335667766963592916772453)
          ·
            refine ⟨34000437706305673671894835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181335667766963592916772453 34000437706305673671894835)
            ·
              refine ⟨51000656559458510507842253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34000437706305673671894835 51000656559458510507842253)
              ·
                refine ⟨19125246209796941440440845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51000656559458510507842253 19125246209796941440440845)
                ·
                  refine ⟨7171967328673853040165317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19125246209796941440440845 7171967328673853040165317)
                  ·
                    refine ⟨1344743874126347445030997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7171967328673853040165317 1344743874126347445030997)
                    ·
                      rfl

theorem cell22_3928319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_3928319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928319 prefixEnd_3928319 := by exact prefixLift 3928319
  have htrace : WordTrace (prefixWord ++ tailWord_3928319) baseStart_3928319 baseEnd_3928319 := by
    simpa [prefixWord, tailWord_3928319, baseEnd_3928319] using wordTrace_append hprefix tailTrace_3928319
  have hstable : (prefixWord ++ tailWord_3928319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928319).length < 2 ^ (prefixWord ++ tailWord_3928319).sum := by decide
  have hdescent : baseEnd_3928319 < baseStart_3928319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928327 : List Nat := [1, 1, 4, 5, 1, 1, 2, 3, 1, 3]
def baseStart_3928327 : Nat := 118140960795 + 3928327 * 2 ^ 59
def prefixEnd_3928327 : Nat := 4983230072969 + 3 ^ 40 * 3928327 * 2
def baseEnd_3928327 : Nat := 1344746612689838090830973

theorem tailTrace_3928327 : CollatzResearch.WordTrace tailWord_3928327 prefixEnd_3928327 1344746612689838090830973 := by
  unfold tailWord_3928327
  simp only [CollatzResearch.WordTrace]
  refine ⟨143277856439349658683247235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95518570959566439122164823 143277856439349658683247235)
  ·
    refine ⟨214916784659024488024870853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143277856439349658683247235 214916784659024488024870853)
    ·
      refine ⟨40296897123567091504663285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214916784659024488024870853 40296897123567091504663285)
      ·
        refine ⟨3777834105334414828562183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40296897123567091504663285 3777834105334414828562183)
        ·
          refine ⟨5666751158001622242843275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3777834105334414828562183 5666751158001622242843275)
          ·
            refine ⟨8500126737002433364264913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5666751158001622242843275 8500126737002433364264913)
            ·
              refine ⟨6375095052751825023198685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8500126737002433364264913 6375095052751825023198685)
              ·
                refine ⟨2390660644781934383699507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6375095052751825023198685 2390660644781934383699507)
                ·
                  refine ⟨3585990967172901575549261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2390660644781934383699507 3585990967172901575549261)
                  ·
                    refine ⟨1344746612689838090830973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3585990967172901575549261 1344746612689838090830973)
                    ·
                      rfl

theorem cell22_3928327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_3928327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928327 prefixEnd_3928327 := by exact prefixLift 3928327
  have htrace : WordTrace (prefixWord ++ tailWord_3928327) baseStart_3928327 baseEnd_3928327 := by
    simpa [prefixWord, tailWord_3928327, baseEnd_3928327] using wordTrace_append hprefix tailTrace_3928327
  have hstable : (prefixWord ++ tailWord_3928327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928327).length < 2 ^ (prefixWord ++ tailWord_3928327).sum := by decide
  have hdescent : baseEnd_3928327 < baseStart_3928327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928334 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 8]
def baseStart_3928334 : Nat := 118140960795 + 3928334 * 2 ^ 59
def prefixEnd_3928334 : Nat := 4983230072969 + 3 ^ 40 * 3928334 * 2
def baseEnd_3928334 : Nat := 448249669644297468635317

theorem tailTrace_3928334 : CollatzResearch.WordTrace tailWord_3928334 prefixEnd_3928334 448249669644297468635317 := by
  unfold tailWord_3928334
  simp only [CollatzResearch.WordTrace]
  refine ⟨17909763968790537359844007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95518741166882865919168037 17909763968790537359844007)
  ·
    refine ⟨26864645953185806039766011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17909763968790537359844007 26864645953185806039766011)
    ·
      refine ⟨40296968929778709059649017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26864645953185806039766011 40296968929778709059649017)
      ·
        refine ⟨30222726697334031794736763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40296968929778709059649017 30222726697334031794736763)
        ·
          refine ⟨45334090046001047692105145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30222726697334031794736763 45334090046001047692105145)
          ·
            refine ⟨34000567534500785769078859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45334090046001047692105145 34000567534500785769078859)
            ·
              refine ⟨51000851301751178653618289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34000567534500785769078859 51000851301751178653618289)
              ·
                refine ⟨38250638476313383990213717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51000851301751178653618289 38250638476313383990213717)
                ·
                  refine ⟨448249669644297468635317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38250638476313383990213717 448249669644297468635317)
                  ·
                    rfl

theorem cell22_3928334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_3928334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928334 prefixEnd_3928334 := by exact prefixLift 3928334
  have htrace : WordTrace (prefixWord ++ tailWord_3928334) baseStart_3928334 baseEnd_3928334 := by
    simpa [prefixWord, tailWord_3928334, baseEnd_3928334] using wordTrace_append hprefix tailTrace_3928334
  have hstable : (prefixWord ++ tailWord_3928334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928334).length < 2 ^ (prefixWord ++ tailWord_3928334).sum := by decide
  have hdescent : baseEnd_3928334 < baseStart_3928334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928351 : List Nat := [1, 1, 2, 4, 3, 2, 2, 1, 6]
def baseStart_3928351 : Nat := 118140960795 + 3928351 * 2 ^ 59
def prefixEnd_3928351 : Nat := 4983230072969 + 3 ^ 40 * 3928351 * 2
def baseEnd_3928351 : Nat := 448251609460103342743633

theorem tailTrace_3928351 : CollatzResearch.WordTrace tailWord_3928351 prefixEnd_3928351 448251609460103342743633 := by
  unfold tailWord_3928351
  simp only [CollatzResearch.WordTrace]
  refine ⟨143278731791262710782120907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95519154527508473854747271 143278731791262710782120907)
  ·
    refine ⟨214918097686894066173181361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143278731791262710782120907 214918097686894066173181361)
    ·
      refine ⟨161188573265170549629886021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214918097686894066173181361 161188573265170549629886021)
      ·
        refine ⟨30222857487219478055603629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161188573265170549629886021 30222857487219478055603629)
        ·
          refine ⟨11333571557707304270851361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30222857487219478055603629 11333571557707304270851361)
          ·
            refine ⟨8500178668280478203138521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11333571557707304270851361 8500178668280478203138521)
            ·
              refine ⟨6375134001210358652353891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8500178668280478203138521 6375134001210358652353891)
              ·
                refine ⟨9562701001815537978530837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6375134001210358652353891 9562701001815537978530837)
                ·
                  refine ⟨448251609460103342743633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9562701001815537978530837 448251609460103342743633)
                  ·
                    rfl

theorem cell22_3928351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 6].length) (baseStart_3928351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928351 prefixEnd_3928351 := by exact prefixLift 3928351
  have htrace : WordTrace (prefixWord ++ tailWord_3928351) baseStart_3928351 baseEnd_3928351 := by
    simpa [prefixWord, tailWord_3928351, baseEnd_3928351] using wordTrace_append hprefix tailTrace_3928351
  have hstable : (prefixWord ++ tailWord_3928351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928351).length < 2 ^ (prefixWord ++ tailWord_3928351).sum := by decide
  have hdescent : baseEnd_3928351 < baseStart_3928351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928364 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 1, 6]
def baseStart_3928364 : Nat := 118140960795 + 3928364 * 2 ^ 59
def prefixEnd_3928364 : Nat := 4983230072969 + 3 ^ 40 * 3928364 * 2
def baseEnd_3928364 : Nat := 1344759278545982327655859

theorem tailTrace_3928364 : CollatzResearch.WordTrace tailWord_3928364 prefixEnd_3928364 1344759278545982327655859 := by
  unfold tailWord_3928364
  simp only [CollatzResearch.WordTrace]
  refine ⟨71639602970107807001172073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95519470626810409334896097 71639602970107807001172073)
  ·
    refine ⟨53729702227580855250879055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71639602970107807001172073 53729702227580855250879055)
    ·
      refine ⟨80594553341371282876318583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53729702227580855250879055 80594553341371282876318583)
      ·
        refine ⟨120891830012056924314477875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80594553341371282876318583 120891830012056924314477875)
        ·
          refine ⟨181337745018085386471716813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120891830012056924314477875 181337745018085386471716813)
          ·
            refine ⟨68001654381782019926893805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181337745018085386471716813 68001654381782019926893805)
            ·
              refine ⟨25500620393168257472585177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68001654381782019926893805 25500620393168257472585177)
              ·
                refine ⟨19125465294876193104438883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25500620393168257472585177 19125465294876193104438883)
                ·
                  refine ⟨28688197942314289656658325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19125465294876193104438883 28688197942314289656658325)
                  ·
                    refine ⟨1344759278545982327655859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28688197942314289656658325 1344759278545982327655859)
                    ·
                      rfl

theorem cell22_3928364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_3928364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928364 prefixEnd_3928364 := by exact prefixLift 3928364
  have htrace : WordTrace (prefixWord ++ tailWord_3928364) baseStart_3928364 baseEnd_3928364 := by
    simpa [prefixWord, tailWord_3928364, baseEnd_3928364] using wordTrace_append hprefix tailTrace_3928364
  have hstable : (prefixWord ++ tailWord_3928364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928364).length < 2 ^ (prefixWord ++ tailWord_3928364).sum := by decide
  have hdescent : baseEnd_3928364 < baseStart_3928364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928409 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 2, 6]
def baseStart_3928409 : Nat := 118140960795 + 3928409 * 2 ^ 59
def prefixEnd_3928409 : Nat := 4983230072969 + 3 ^ 40 * 3928409 * 2
def baseEnd_3928409 : Nat := 1344774682965617210280721

theorem tailTrace_3928409 : CollatzResearch.WordTrace tailWord_3928409 prefixEnd_3928409 1344774682965617210280721 := by
  unfold tailWord_3928409
  simp only [CollatzResearch.WordTrace]
  refine ⟨143280847225052586687732281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95520564816701724458488187 143280847225052586687732281)
  ·
    refine ⟨107460635418789440015799211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143280847225052586687732281 107460635418789440015799211)
    ·
      refine ⟨161190953128184160023698817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107460635418789440015799211 161190953128184160023698817)
      ·
        refine ⟨120893214846138120017774113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161190953128184160023698817 120893214846138120017774113)
        ·
          refine ⟨90669911134603590013330585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120893214846138120017774113 90669911134603590013330585)
          ·
            refine ⟨68002433350952692509997939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90669911134603590013330585 68002433350952692509997939)
            ·
              refine ⟨102003650026429038764996909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68002433350952692509997939 102003650026429038764996909)
              ·
                refine ⟨38251368759910889536873841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102003650026429038764996909 38251368759910889536873841)
                ·
                  refine ⟨28688526569933167152655381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38251368759910889536873841 28688526569933167152655381)
                  ·
                    refine ⟨1344774682965617210280721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28688526569933167152655381 1344774682965617210280721)
                    ·
                      rfl

theorem cell22_3928409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_3928409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928409 prefixEnd_3928409 := by exact prefixLift 3928409
  have htrace : WordTrace (prefixWord ++ tailWord_3928409) baseStart_3928409 baseEnd_3928409 := by
    simpa [prefixWord, tailWord_3928409, baseEnd_3928409] using wordTrace_append hprefix tailTrace_3928409
  have hstable : (prefixWord ++ tailWord_3928409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928409).length < 2 ^ (prefixWord ++ tailWord_3928409).sum := by decide
  have hdescent : baseEnd_3928409 < baseStart_3928409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928439 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 3, 7]
def baseStart_3928439 : Nat := 118140960795 + 3928439 * 2 ^ 59
def prefixEnd_3928439 : Nat := 4983230072969 + 3 ^ 40 * 3928439 * 2
def baseEnd_3928439 : Nat := 1344784952578707132030629

theorem tailTrace_3928439 : CollatzResearch.WordTrace tailWord_3928439 prefixEnd_3928439 1344784952578707132030629 := by
  unfold tailWord_3928439
  simp only [CollatzResearch.WordTrace]
  refine ⟨143281941414943901811324371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95521294276629267874216247 143281941414943901811324371)
  ·
    refine ⟨214922912122415852716986557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143281941414943901811324371 214922912122415852716986557)
    ·
      refine ⟨80596092045905944768869959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214922912122415852716986557 80596092045905944768869959)
      ·
        refine ⟨120894138068858917153304939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80596092045905944768869959 120894138068858917153304939)
        ·
          refine ⟨181341207103288375729957409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120894138068858917153304939 181341207103288375729957409)
          ·
            refine ⟨136005905327466281797468057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181341207103288375729957409 136005905327466281797468057)
            ·
              refine ⟨102004428995599711348101043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136005905327466281797468057 102004428995599711348101043)
              ·
                refine ⟨153006643493399567022151565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102004428995599711348101043 153006643493399567022151565)
                ·
                  refine ⟨57377491310024837633306837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153006643493399567022151565 57377491310024837633306837)
                  ·
                    refine ⟨1344784952578707132030629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57377491310024837633306837 1344784952578707132030629)
                    ·
                      rfl

theorem cell22_3928439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_3928439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928439 prefixEnd_3928439 := by exact prefixLift 3928439
  have htrace : WordTrace (prefixWord ++ tailWord_3928439) baseStart_3928439 baseEnd_3928439 := by
    simpa [prefixWord, tailWord_3928439, baseEnd_3928439] using wordTrace_append hprefix tailTrace_3928439
  have hstable : (prefixWord ++ tailWord_3928439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928439).length < 2 ^ (prefixWord ++ tailWord_3928439).sum := by decide
  have hdescent : baseEnd_3928439 < baseStart_3928439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928456 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 2, 5]
def baseStart_3928456 : Nat := 118140960795 + 3928456 * 2 ^ 59
def prefixEnd_3928456 : Nat := 4983230072969 + 3 ^ 40 * 3928456 * 2
def baseEnd_3928456 : Nat := 1344790772026124754355577

theorem tailTrace_3928456 : CollatzResearch.WordTrace tailWord_3928456 prefixEnd_3928456 1344790772026124754355577 := by
  unfold tailWord_3928456
  simp only [CollatzResearch.WordTrace]
  refine ⟨71641280727941156857346611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95521707637254875809795481 71641280727941156857346611)
  ·
    refine ⟨107461921091911735286019917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71641280727941156857346611 107461921091911735286019917)
    ·
      refine ⟨40298220409466900732257469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107461921091911735286019917 40298220409466900732257469)
      ·
        refine ⟨15111832653550087774596551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40298220409466900732257469 15111832653550087774596551)
        ·
          refine ⟨22667748980325131661894827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15111832653550087774596551 22667748980325131661894827)
          ·
            refine ⟨34001623470487697492842241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22667748980325131661894827 34001623470487697492842241)
            ·
              refine ⟨25501217602865773119631681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34001623470487697492842241 25501217602865773119631681)
              ·
                refine ⟨19125913202149329839723761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25501217602865773119631681 19125913202149329839723761)
                ·
                  refine ⟨14344434901611997379792821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19125913202149329839723761 14344434901611997379792821)
                  ·
                    refine ⟨1344790772026124754355577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14344434901611997379792821 1344790772026124754355577)
                    ·
                      rfl

theorem cell22_3928456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_3928456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928456 prefixEnd_3928456 := by exact prefixLift 3928456
  have htrace : WordTrace (prefixWord ++ tailWord_3928456) baseStart_3928456 baseEnd_3928456 := by
    simpa [prefixWord, tailWord_3928456, baseEnd_3928456] using wordTrace_append hprefix tailTrace_3928456
  have hstable : (prefixWord ++ tailWord_3928456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928456).length < 2 ^ (prefixWord ++ tailWord_3928456).sum := by decide
  have hdescent : baseEnd_3928456 < baseStart_3928456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928462 : List Nat := [4, 1, 1, 4, 1, 2, 1, 4, 1, 3]
def baseStart_3928462 : Nat := 118140960795 + 3928462 * 2 ^ 59
def prefixEnd_3928462 : Nat := 4983230072969 + 3 ^ 40 * 3928462 * 2
def baseEnd_3928462 : Nat := 1344792825948742738705559

theorem tailTrace_3928462 : CollatzResearch.WordTrace tailWord_3928462 prefixEnd_3928462 1344792825948742738705559 := by
  unfold tailWord_3928462
  simp only [CollatzResearch.WordTrace]
  refine ⟨17910347536732572092426455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95521853529240384492941093 17910347536732572092426455)
  ·
    refine ⟨26865521305098858138639683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17910347536732572092426455 26865521305098858138639683)
    ·
      refine ⟨40298281957648287207959525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26865521305098858138639683 40298281957648287207959525)
      ·
        refine ⟨7555927867059053851492411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40298281957648287207959525 7555927867059053851492411)
        ·
          refine ⟨11333891800588580777238617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7555927867059053851492411 11333891800588580777238617)
          ·
            refine ⟨8500418850441435582928963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11333891800588580777238617 8500418850441435582928963)
            ·
              refine ⟨12750628275662153374393445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8500418850441435582928963 12750628275662153374393445)
              ·
                refine ⟨2390742801686653757698771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12750628275662153374393445 2390742801686653757698771)
                ·
                  refine ⟨3586114202529980636548157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2390742801686653757698771 3586114202529980636548157)
                  ·
                    refine ⟨1344792825948742738705559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3586114202529980636548157 1344792825948742738705559)
                    ·
                      rfl

theorem cell22_3928462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_3928462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928462 prefixEnd_3928462 := by exact prefixLift 3928462
  have htrace : WordTrace (prefixWord ++ tailWord_3928462) baseStart_3928462 baseEnd_3928462 := by
    simpa [prefixWord, tailWord_3928462, baseEnd_3928462] using wordTrace_append hprefix tailTrace_3928462
  have hstable : (prefixWord ++ tailWord_3928462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928462).length < 2 ^ (prefixWord ++ tailWord_3928462).sum := by decide
  have hdescent : baseEnd_3928462 < baseStart_3928462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928471 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 3, 4]
def baseStart_3928471 : Nat := 118140960795 + 3928471 * 2 ^ 59
def prefixEnd_3928471 : Nat := 4983230072969 + 3 ^ 40 * 3928471 * 2
def baseEnd_3928471 : Nat := 1344795906832669715230531

theorem tailTrace_3928471 : CollatzResearch.WordTrace tailWord_3928471 prefixEnd_3928471 1344795906832669715230531 := by
  unfold tailWord_3928471
  simp only [CollatzResearch.WordTrace]
  refine ⟨143283108550827971276489267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95522072367218647517659511 143283108550827971276489267)
  ·
    refine ⟨214924662826241956914733901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143283108550827971276489267 214924662826241956914733901)
    ·
      refine ⟨80596748559840733843025213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214924662826241956914733901 80596748559840733843025213)
      ·
        refine ⟨30223780709940275191134455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80596748559840733843025213 30223780709940275191134455)
        ·
          refine ⟨45335671064910412786701683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30223780709940275191134455 45335671064910412786701683)
          ·
            refine ⟨68003506597365619180052525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45335671064910412786701683 68003506597365619180052525)
            ·
              refine ⟨25501314974012107192519697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68003506597365619180052525 25501314974012107192519697)
              ·
                refine ⟨19125986230509080394389773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25501314974012107192519697 19125986230509080394389773)
                ·
                  refine ⟨7172244836440905147896165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19125986230509080394389773 7172244836440905147896165)
                  ·
                    refine ⟨1344795906832669715230531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7172244836440905147896165 1344795906832669715230531)
                    ·
                      rfl

theorem cell22_3928471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_3928471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928471 prefixEnd_3928471 := by exact prefixLift 3928471
  have htrace : WordTrace (prefixWord ++ tailWord_3928471) baseStart_3928471 baseEnd_3928471 := by
    simpa [prefixWord, tailWord_3928471, baseEnd_3928471] using wordTrace_append hprefix tailTrace_3928471
  have hstable : (prefixWord ++ tailWord_3928471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928471).length < 2 ^ (prefixWord ++ tailWord_3928471).sum := by decide
  have hdescent : baseEnd_3928471 < baseStart_3928471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928503 : List Nat := [1, 1, 3, 1, 3, 3, 1, 5, 4]
def baseStart_3928503 : Nat := 118140960795 + 3928503 * 2 ^ 59
def prefixEnd_3928503 : Nat := 4983230072969 + 3 ^ 40 * 3928503 * 2
def baseEnd_3928503 : Nat := 448268953695544099476811

theorem tailTrace_3928503 : CollatzResearch.WordTrace tailWord_3928503 prefixEnd_3928503 448268953695544099476811 := by
  unfold tailWord_3928503
  simp only [CollatzResearch.WordTrace]
  refine ⟨143284275686712040741654163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95522850457808027161102775 143284275686712040741654163)
  ·
    refine ⟨214926413530068061112481245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143284275686712040741654163 214926413530068061112481245)
    ·
      refine ⟨80597405073775522917180467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214926413530068061112481245 80597405073775522917180467)
      ·
        refine ⟨120896107610663284375770701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80597405073775522917180467 120896107610663284375770701)
        ·
          refine ⟨45336040353998731640914013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120896107610663284375770701 45336040353998731640914013)
          ·
            refine ⟨17001015132749524365342755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45336040353998731640914013 17001015132749524365342755)
            ·
              refine ⟨25501522699124286548014133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17001015132749524365342755 25501522699124286548014133)
              ·
                refine ⟨2390767753042901863876325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25501522699124286548014133 2390767753042901863876325)
                ·
                  refine ⟨448268953695544099476811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2390767753042901863876325 448268953695544099476811)
                  ·
                    rfl

theorem cell22_3928503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 4].length) (baseStart_3928503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928503 prefixEnd_3928503 := by exact prefixLift 3928503
  have htrace : WordTrace (prefixWord ++ tailWord_3928503) baseStart_3928503 baseEnd_3928503 := by
    simpa [prefixWord, tailWord_3928503, baseEnd_3928503] using wordTrace_append hprefix tailTrace_3928503
  have hstable : (prefixWord ++ tailWord_3928503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928503).length < 2 ^ (prefixWord ++ tailWord_3928503).sum := by decide
  have hdescent : baseEnd_3928503 < baseStart_3928503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928505 : List Nat := [1, 2, 1, 4, 3, 1, 4, 1, 1, 4]
def baseStart_3928505 : Nat := 118140960795 + 3928505 * 2 ^ 59
def prefixEnd_3928505 : Nat := 4983230072969 + 3 ^ 40 * 3928505 * 2
def baseEnd_3928505 : Nat := 1344807545727504959880427

theorem tailTrace_3928505 : CollatzResearch.WordTrace tailWord_3928505 prefixEnd_3928505 1344807545727504959880427 := by
  unfold tailWord_3928505
  simp only [CollatzResearch.WordTrace]
  refine ⟨143284348632704795083226969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95522899088469863388817979 143284348632704795083226969)
  ·
    refine ⟨107463261474528596312420227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143284348632704795083226969 107463261474528596312420227)
    ·
      refine ⟨161194892211792894468630341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107463261474528596312420227 161194892211792894468630341)
      ·
        refine ⟨30224042289711167712868189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161194892211792894468630341 30224042289711167712868189)
        ·
          refine ⟨11334015858641687892325571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30224042289711167712868189 11334015858641687892325571)
          ·
            refine ⟨17001023787962531838488357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11334015858641687892325571 17001023787962531838488357)
            ·
              refine ⟨3187691960242974719716567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17001023787962531838488357 3187691960242974719716567)
              ·
                refine ⟨4781537940364462079574851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3187691960242974719716567 4781537940364462079574851)
                ·
                  refine ⟨7172306910546693119362277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4781537940364462079574851 7172306910546693119362277)
                  ·
                    refine ⟨1344807545727504959880427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7172306910546693119362277 1344807545727504959880427)
                    ·
                      rfl

theorem cell22_3928505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 1, 4].length) (baseStart_3928505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928505 prefixEnd_3928505 := by exact prefixLift 3928505
  have htrace : WordTrace (prefixWord ++ tailWord_3928505) baseStart_3928505 baseEnd_3928505 := by
    simpa [prefixWord, tailWord_3928505, baseEnd_3928505] using wordTrace_append hprefix tailTrace_3928505
  have hstable : (prefixWord ++ tailWord_3928505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928505).length < 2 ^ (prefixWord ++ tailWord_3928505).sum := by decide
  have hdescent : baseEnd_3928505 < baseStart_3928505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928565 : List Nat := [1, 3, 5, 1, 2, 2, 8]
def baseStart_3928565 : Nat := 118140960795 + 3928565 * 2 ^ 59
def prefixEnd_3928565 : Nat := 4983230072969 + 3 ^ 40 * 3928565 * 2
def baseEnd_3928565 : Nat := 49808447590877214940009

theorem tailTrace_3928565 : CollatzResearch.WordTrace tailWord_3928565 prefixEnd_3928565 49808447590877214940009 := by
  unfold tailWord_3928565
  simp only [CollatzResearch.WordTrace]
  refine ⟨143286537012487425330411149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95524358008324950220274099 143286537012487425330411149)
  ·
    refine ⟨53732451379682784498904181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143286537012487425330411149 53732451379682784498904181)
    ·
      refine ⟨5037417316845261046772267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53732451379682784498904181 5037417316845261046772267)
      ·
        refine ⟨7556125975267891570158401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5037417316845261046772267 7556125975267891570158401)
        ·
          refine ⟨5667094481450918677618801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7556125975267891570158401 5667094481450918677618801)
          ·
            refine ⟨4250320861088189008214101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5667094481450918677618801 4250320861088189008214101)
            ·
              refine ⟨49808447590877214940009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4250320861088189008214101 49808447590877214940009)
              ·
                rfl

theorem cell22_3928565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 8].length) (baseStart_3928565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928565 prefixEnd_3928565 := by exact prefixLift 3928565
  have htrace : WordTrace (prefixWord ++ tailWord_3928565) baseStart_3928565 baseEnd_3928565 := by
    simpa [prefixWord, tailWord_3928565, baseEnd_3928565] using wordTrace_append hprefix tailTrace_3928565
  have hstable : (prefixWord ++ tailWord_3928565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928565).length < 2 ^ (prefixWord ++ tailWord_3928565).sum := by decide
  have hdescent : baseEnd_3928565 < baseStart_3928565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928582 : List Nat := [6, 2, 1, 1, 1, 1, 1, 9]
def baseStart_3928582 : Nat := 118140960795 + 3928582 * 2 ^ 59
def prefixEnd_3928582 : Nat := 4983230072969 + 3 ^ 40 * 3928582 * 2
def baseEnd_3928582 : Nat := 149425989377900269522799

theorem tailTrace_3928582 : CollatzResearch.WordTrace tailWord_3928582 prefixEnd_3928582 149425989377900269522799 := by
  unfold tailWord_3928582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4477723657919557413555625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95524771368950558155853333 4477723657919557413555625)
  ·
    refine ⟨3358292743439668060166719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4477723657919557413555625 3358292743439668060166719)
    ·
      refine ⟨5037439115159502090250079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3358292743439668060166719 5037439115159502090250079)
      ·
        refine ⟨7556158672739253135375119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5037439115159502090250079 7556158672739253135375119)
        ·
          refine ⟨11334238009108879703062679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7556158672739253135375119 11334238009108879703062679)
          ·
            refine ⟨17001357013663319554594019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11334238009108879703062679 17001357013663319554594019)
            ·
              refine ⟨25502035520494979331891029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17001357013663319554594019 25502035520494979331891029)
              ·
                refine ⟨149425989377900269522799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25502035520494979331891029 149425989377900269522799)
                ·
                  rfl

theorem cell22_3928582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_3928582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928582 prefixEnd_3928582 := by exact prefixLift 3928582
  have htrace : WordTrace (prefixWord ++ tailWord_3928582) baseStart_3928582 baseEnd_3928582 := by
    simpa [prefixWord, tailWord_3928582, baseEnd_3928582] using wordTrace_append hprefix tailTrace_3928582
  have hstable : (prefixWord ++ tailWord_3928582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928582).length < 2 ^ (prefixWord ++ tailWord_3928582).sum := by decide
  have hdescent : baseEnd_3928582 < baseStart_3928582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928674 : List Nat := [3, 3, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_3928674 : Nat := 118140960795 + 3928674 * 2 ^ 59
def prefixEnd_3928674 : Nat := 4983230072969 + 3 ^ 40 * 3928674 * 2
def baseEnd_3928674 : Nat := 1344865397881244852404909

theorem tailTrace_3928674 : CollatzResearch.WordTrace tailWord_3928674 prefixEnd_3928674 1344865397881244852404909 := by
  unfold tailWord_3928674
  simp only [CollatzResearch.WordTrace]
  refine ⟨35822628142273134236532269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95527008379395024630752717 35822628142273134236532269)
  ·
    refine ⟨13433485553352425338699601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35822628142273134236532269 13433485553352425338699601)
    ·
      refine ⟨10075114165014319004024701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13433485553352425338699601 10075114165014319004024701)
      ·
        refine ⟨3778167811880369626509263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10075114165014319004024701 3778167811880369626509263)
        ·
          refine ⟨5667251717820554439763895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3778167811880369626509263 5667251717820554439763895)
          ·
            refine ⟨8500877576730831659645843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5667251717820554439763895 8500877576730831659645843)
            ·
              refine ⟨12751316365096247489468765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8500877576730831659645843 12751316365096247489468765)
              ·
                refine ⟨4781743636911092808550787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12751316365096247489468765 4781743636911092808550787)
                ·
                  refine ⟨7172615455366639212826181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4781743636911092808550787 7172615455366639212826181)
                  ·
                    refine ⟨1344865397881244852404909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7172615455366639212826181 1344865397881244852404909)
                    ·
                      rfl

theorem cell22_3928674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_3928674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928674 prefixEnd_3928674 := by exact prefixLift 3928674
  have htrace : WordTrace (prefixWord ++ tailWord_3928674) baseStart_3928674 baseEnd_3928674 := by
    simpa [prefixWord, tailWord_3928674, baseEnd_3928674] using wordTrace_append hprefix tailTrace_3928674
  have hstable : (prefixWord ++ tailWord_3928674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928674).length < 2 ^ (prefixWord ++ tailWord_3928674).sum := by decide
  have hdescent : baseEnd_3928674 < baseStart_3928674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928728 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 9]
def baseStart_3928728 : Nat := 118140960795 + 3928728 * 2 ^ 59
def prefixEnd_3928728 : Nat := 4983230072969 + 3 ^ 40 * 3928728 * 2
def baseEnd_3928728 : Nat := 448294627728268903851581

theorem tailTrace_3928728 : CollatzResearch.WordTrace tailWord_3928728 prefixEnd_3928728 448294627728268903851581 := by
  unfold tailWord_3928728
  simp only [CollatzResearch.WordTrace]
  refine ⟨71646241055448452084297419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95528321407264602779063225 71646241055448452084297419)
  ·
    refine ⟨107469361583172678126446129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71646241055448452084297419 107469361583172678126446129)
    ·
      refine ⟨80602021187379508594834597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107469361583172678126446129 80602021187379508594834597)
      ·
        refine ⟨15112878972633657861531487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80602021187379508594834597 15112878972633657861531487)
        ·
          refine ⟨22669318458950486792297231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15112878972633657861531487 22669318458950486792297231)
          ·
            refine ⟨34003977688425730188445847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22669318458950486792297231 34003977688425730188445847)
            ·
              refine ⟨51005966532638595282668771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34003977688425730188445847 51005966532638595282668771)
              ·
                refine ⟨76508949798957892924003157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51005966532638595282668771 76508949798957892924003157)
                ·
                  refine ⟨448294627728268903851581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76508949798957892924003157 448294627728268903851581)
                  ·
                    rfl

theorem cell22_3928728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 9].length) (baseStart_3928728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928728 prefixEnd_3928728 := by exact prefixLift 3928728
  have htrace : WordTrace (prefixWord ++ tailWord_3928728) baseStart_3928728 baseEnd_3928728 := by
    simpa [prefixWord, tailWord_3928728, baseEnd_3928728] using wordTrace_append hprefix tailTrace_3928728
  have hstable : (prefixWord ++ tailWord_3928728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928728).length < 2 ^ (prefixWord ++ tailWord_3928728).sum := by decide
  have hdescent : baseEnd_3928728 < baseStart_3928728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928749 : List Nat := [1, 5, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_3928749 : Nat := 118140960795 + 3928749 * 2 ^ 59
def prefixEnd_3928749 : Nat := 4983230072969 + 3 ^ 40 * 3928749 * 2
def baseEnd_3928749 : Nat := 1344891071913969656779679

theorem tailTrace_3928749 : CollatzResearch.WordTrace tailWord_3928749 prefixEnd_3928749 1344891071913969656779679 := by
  unfold tailWord_3928749
  simp only [CollatzResearch.WordTrace]
  refine ⟨143293248043820824755109301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95528832029213883170072867 143293248043820824755109301)
  ·
    refine ⟨13433742004108202320791497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143293248043820824755109301 13433742004108202320791497)
    ·
      refine ⟨10075306503081151740593623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13433742004108202320791497 10075306503081151740593623)
      ·
        refine ⟨15112959754621727610890435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10075306503081151740593623 15112959754621727610890435)
        ·
          refine ⟨22669439631932591416335653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15112959754621727610890435 22669439631932591416335653)
          ·
            refine ⟨4250519930987360890562935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22669439631932591416335653 4250519930987360890562935)
            ·
              refine ⟨6375779896481041335844403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4250519930987360890562935 6375779896481041335844403)
              ·
                refine ⟨9563669844721562003766605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6375779896481041335844403 9563669844721562003766605)
                ·
                  refine ⟨3586376191770585751412477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9563669844721562003766605 3586376191770585751412477)
                  ·
                    refine ⟨1344891071913969656779679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3586376191770585751412477 1344891071913969656779679)
                    ·
                      rfl

theorem cell22_3928749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_3928749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928749 prefixEnd_3928749 := by exact prefixLift 3928749
  have htrace : WordTrace (prefixWord ++ tailWord_3928749) baseStart_3928749 baseEnd_3928749 := by
    simpa [prefixWord, tailWord_3928749, baseEnd_3928749] using wordTrace_append hprefix tailTrace_3928749
  have hstable : (prefixWord ++ tailWord_3928749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928749).length < 2 ^ (prefixWord ++ tailWord_3928749).sum := by decide
  have hdescent : baseEnd_3928749 < baseStart_3928749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928775 : List Nat := [1, 1, 4, 1, 1, 1, 2, 6, 1, 4]
def baseStart_3928775 : Nat := 118140960795 + 3928775 * 2 ^ 59
def prefixEnd_3928775 : Nat := 4983230072969 + 3 ^ 40 * 3928775 * 2
def baseEnd_3928775 : Nat := 1344899972245314255629599

theorem tailTrace_3928775 : CollatzResearch.WordTrace tailWord_3928775 prefixEnd_3928775 1344899972245314255629599 := by
  unfold tailWord_3928775
  simp only [CollatzResearch.WordTrace]
  refine ⟨143294196341726631195555779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95529464227817754130370519 143294196341726631195555779)
  ·
    refine ⟨214941294512589946793333669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143294196341726631195555779 214941294512589946793333669)
    ·
      refine ⟨40301492721110615023750063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214941294512589946793333669 40301492721110615023750063)
      ·
        refine ⟨60452239081665922535625095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40301492721110615023750063 60452239081665922535625095)
        ·
          refine ⟨90678358622498883803437643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60452239081665922535625095 90678358622498883803437643)
          ·
            refine ⟨136017537933748325705156465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90678358622498883803437643 136017537933748325705156465)
            ·
              refine ⟨102013153450311244278867349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136017537933748325705156465 102013153450311244278867349)
              ·
                refine ⟨4781866567983339575571907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102013153450311244278867349 4781866567983339575571907)
                ·
                  refine ⟨7172799851975009363357861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4781866567983339575571907 7172799851975009363357861)
                  ·
                    refine ⟨1344899972245314255629599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7172799851975009363357861 1344899972245314255629599)
                    ·
                      rfl

theorem cell22_3928775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_3928775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928775 prefixEnd_3928775 := by exact prefixLift 3928775
  have htrace : WordTrace (prefixWord ++ tailWord_3928775) baseStart_3928775 baseEnd_3928775 := by
    simpa [prefixWord, tailWord_3928775, baseEnd_3928775] using wordTrace_append hprefix tailTrace_3928775
  have hstable : (prefixWord ++ tailWord_3928775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928775).length < 2 ^ (prefixWord ++ tailWord_3928775).sum := by decide
  have hdescent : baseEnd_3928775 < baseStart_3928775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928822 : List Nat := [5, 1, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_3928822 : Nat := 118140960795 + 3928822 * 2 ^ 59
def prefixEnd_3928822 : Nat := 4983230072969 + 3 ^ 40 * 3928822 * 2
def baseEnd_3928822 : Nat := 1344916061305821799704455

theorem tailTrace_3928822 : CollatzResearch.WordTrace tailWord_3928822 prefixEnd_3928822 1344916061305821799704455 := by
  unfold tailWord_3928822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8955994410784772388907295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95530607048370905481677813 8955994410784772388907295)
  ·
    refine ⟨13433991616177158583360943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8955994410784772388907295 13433991616177158583360943)
    ·
      refine ⟨20150987424265737875041415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13433991616177158583360943 20150987424265737875041415)
      ·
        refine ⟨30226481136398606812562123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20150987424265737875041415 30226481136398606812562123)
        ·
          refine ⟨45339721704597910218843185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30226481136398606812562123 45339721704597910218843185)
          ·
            refine ⟨34004791278448432664132389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45339721704597910218843185 34004791278448432664132389)
            ·
              refine ⟨6375898364709081124524823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34004791278448432664132389 6375898364709081124524823)
              ·
                refine ⟨9563847547063621686787235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6375898364709081124524823 9563847547063621686787235)
                ·
                  refine ⟨14345771320595432530180853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9563847547063621686787235 14345771320595432530180853)
                  ·
                    refine ⟨1344916061305821799704455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14345771320595432530180853 1344916061305821799704455)
                    ·
                      rfl

theorem cell22_3928822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_3928822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928822 prefixEnd_3928822 := by exact prefixLift 3928822
  have htrace : WordTrace (prefixWord ++ tailWord_3928822) baseStart_3928822 baseEnd_3928822 := by
    simpa [prefixWord, tailWord_3928822, baseEnd_3928822] using wordTrace_append hprefix tailTrace_3928822
  have hstable : (prefixWord ++ tailWord_3928822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928822).length < 2 ^ (prefixWord ++ tailWord_3928822).sum := by decide
  have hdescent : baseEnd_3928822 < baseStart_3928822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928880 : List Nat := [2, 1, 1, 1, 2, 2, 1, 7, 5]
def baseStart_3928880 : Nat := 118140960795 + 3928880 * 2 ^ 59
def prefixEnd_3928880 : Nat := 4983230072969 + 3 ^ 40 * 3928880 * 2
def baseEnd_3928880 : Nat := 448311971963709660584759

theorem tailTrace_3928880 : CollatzResearch.WordTrace tailWord_3928880 prefixEnd_3928880 448311971963709660584759 := by
  unfold tailWord_3928880
  simp only [CollatzResearch.WordTrace]
  refine ⟨71649013003173117064064047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95532017337564156085418729 71649013003173117064064047)
  ·
    refine ⟨107473519504759675596096071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71649013003173117064064047 107473519504759675596096071)
    ·
      refine ⟨161210279257139513394144107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107473519504759675596096071 161210279257139513394144107)
      ·
        refine ⟨241815418885709270091216161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161210279257139513394144107 241815418885709270091216161)
        ·
          refine ⟨181361564164281952568412121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241815418885709270091216161 181361564164281952568412121)
          ·
            refine ⟨136021173123211464426309091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181361564164281952568412121 136021173123211464426309091)
            ·
              refine ⟨204031759684817196639463637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136021173123211464426309091 204031759684817196639463637)
              ·
                refine ⟨4781994367612903046237429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 204031759684817196639463637 4781994367612903046237429)
                ·
                  refine ⟨448311971963709660584759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4781994367612903046237429 448311971963709660584759)
                  ·
                    rfl

theorem cell22_3928880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 5].length) (baseStart_3928880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928880 prefixEnd_3928880 := by exact prefixLift 3928880
  have htrace : WordTrace (prefixWord ++ tailWord_3928880) baseStart_3928880 baseEnd_3928880 := by
    simpa [prefixWord, tailWord_3928880, baseEnd_3928880] using wordTrace_append hprefix tailTrace_3928880
  have hstable : (prefixWord ++ tailWord_3928880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928880).length < 2 ^ (prefixWord ++ tailWord_3928880).sum := by decide
  have hdescent : baseEnd_3928880 < baseStart_3928880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928886 : List Nat := [5, 1, 2, 2, 2, 2, 2, 6]
def baseStart_3928886 : Nat := 118140960795 + 3928886 * 2 ^ 59
def prefixEnd_3928886 : Nat := 4983230072969 + 3 ^ 40 * 3928886 * 2
def baseEnd_3928886 : Nat := 149437552201527440678251

theorem tailTrace_3928886 : CollatzResearch.WordTrace tailWord_3928886 prefixEnd_3928886 149437552201527440678251 := by
  unfold tailWord_3928886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8956140302770281072052907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95532163229549664768564341 8956140302770281072052907)
  ·
    refine ⟨13434210454155421608079361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8956140302770281072052907 13434210454155421608079361)
    ·
      refine ⟨10075657840616566206059521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13434210454155421608079361 10075657840616566206059521)
      ·
        refine ⟨7556743380462424654544641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10075657840616566206059521 7556743380462424654544641)
        ·
          refine ⟨5667557535346818490908481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7556743380462424654544641 5667557535346818490908481)
          ·
            refine ⟨4250668151510113868181361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5667557535346818490908481 4250668151510113868181361)
            ·
              refine ⟨3188001113632585401136021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4250668151510113868181361 3188001113632585401136021)
              ·
                refine ⟨149437552201527440678251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3188001113632585401136021 149437552201527440678251)
                ·
                  rfl

theorem cell22_3928886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_3928886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928886 prefixEnd_3928886 := by exact prefixLift 3928886
  have htrace : WordTrace (prefixWord ++ tailWord_3928886) baseStart_3928886 baseEnd_3928886 := by
    simpa [prefixWord, tailWord_3928886, baseEnd_3928886] using wordTrace_append hprefix tailTrace_3928886
  have hstable : (prefixWord ++ tailWord_3928886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928886).length < 2 ^ (prefixWord ++ tailWord_3928886).sum := by decide
  have hdescent : baseEnd_3928886 < baseStart_3928886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928955 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 1, 6]
def baseStart_3928955 : Nat := 118140960795 + 3928955 * 2 ^ 59
def prefixEnd_3928955 : Nat := 4983230072969 + 3 ^ 40 * 3928955 * 2
def baseEnd_3928955 : Nat := 1344961589923853786129047

theorem tailTrace_3928955 : CollatzResearch.WordTrace tailWord_3928955 prefixEnd_3928955 1344961589923853786129047 := by
  unfold tailWord_3928955
  simp only [CollatzResearch.WordTrace]
  refine ⟨143300761481074521937108319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95533840987383014624738879 143300761481074521937108319)
  ·
    refine ⟨214951142221611782905662479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143300761481074521937108319 214951142221611782905662479)
    ·
      refine ⟨322426713332417674358493719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214951142221611782905662479 322426713332417674358493719)
      ·
        refine ⟨483640069998626511537740579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322426713332417674358493719 483640069998626511537740579)
        ·
          refine ⟨725460104997939767306610869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483640069998626511537740579 725460104997939767306610869)
          ·
            refine ⟨68011884843556853184994769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 725460104997939767306610869 68011884843556853184994769)
            ·
              refine ⟨51008913632667639888746077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68011884843556853184994769 51008913632667639888746077)
              ·
                refine ⟨19128342612250364958279779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51008913632667639888746077 19128342612250364958279779)
                ·
                  refine ⟨28692513918375547437419669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19128342612250364958279779 28692513918375547437419669)
                  ·
                    refine ⟨1344961589923853786129047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28692513918375547437419669 1344961589923853786129047)
                    ·
                      rfl

theorem cell22_3928955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 6].length) (baseStart_3928955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928955 prefixEnd_3928955 := by exact prefixLift 3928955
  have htrace : WordTrace (prefixWord ++ tailWord_3928955) baseStart_3928955 baseEnd_3928955 := by
    simpa [prefixWord, tailWord_3928955, baseEnd_3928955] using wordTrace_append hprefix tailTrace_3928955
  have hstable : (prefixWord ++ tailWord_3928955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928955).length < 2 ^ (prefixWord ++ tailWord_3928955).sum := by decide
  have hdescent : baseEnd_3928955 < baseStart_3928955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928957 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 6, 3]
def baseStart_3928957 : Nat := 118140960795 + 3928957 * 2 ^ 59
def prefixEnd_3928957 : Nat := 4983230072969 + 3 ^ 40 * 3928957 * 2
def baseEnd_3928957 : Nat := 1344962274564726447579041

theorem tailTrace_3928957 : CollatzResearch.WordTrace tailWord_3928957 prefixEnd_3928957 1344962274564726447579041 := by
  unfold tailWord_3928957
  simp only [CollatzResearch.WordTrace]
  refine ⟨143300834427067276278681125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95533889618044850852454083 143300834427067276278681125)
  ·
    refine ⟨26868906455075114302252711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143300834427067276278681125 26868906455075114302252711)
    ·
      refine ⟨40303359682612671453379067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26868906455075114302252711 40303359682612671453379067)
      ·
        refine ⟨60455039523919007180068601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40303359682612671453379067 60455039523919007180068601)
        ·
          refine ⟨45341279642939255385051451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60455039523919007180068601 45341279642939255385051451)
          ·
            refine ⟨68011919464408883077577177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45341279642939255385051451 68011919464408883077577177)
            ·
              refine ⟨51008939598306662308182883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68011919464408883077577177 51008939598306662308182883)
              ·
                refine ⟨76513409397459993462274325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51008939598306662308182883 76513409397459993462274325)
                ·
                  refine ⟨3586566065505937193544109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76513409397459993462274325 3586566065505937193544109)
                  ·
                    refine ⟨1344962274564726447579041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3586566065505937193544109 1344962274564726447579041)
                    ·
                      rfl

theorem cell22_3928957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_3928957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928957 prefixEnd_3928957 := by exact prefixLift 3928957
  have htrace : WordTrace (prefixWord ++ tailWord_3928957) baseStart_3928957 baseEnd_3928957 := by
    simpa [prefixWord, tailWord_3928957, baseEnd_3928957] using wordTrace_append hprefix tailTrace_3928957
  have hstable : (prefixWord ++ tailWord_3928957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928957).length < 2 ^ (prefixWord ++ tailWord_3928957).sum := by decide
  have hdescent : baseEnd_3928957 < baseStart_3928957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928972 : List Nat := [2, 2, 1, 2, 1, 2, 4, 2, 2, 4]
def baseStart_3928972 : Nat := 118140960795 + 3928972 * 2 ^ 59
def prefixEnd_3928972 : Nat := 4983230072969 + 3 ^ 40 * 3928972 * 2
def baseEnd_3928972 : Nat := 1344967409371271408453995

theorem tailTrace_3928972 : CollatzResearch.WordTrace tailWord_3928972 prefixEnd_3928972 1344967409371271408453995 := by
  unfold tailWord_3928972
  simp only [CollatzResearch.WordTrace]
  refine ⟨71650690761006466920238585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95534254348008622560318113 71650690761006466920238585)
  ·
    refine ⟨53738018070754850190178939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71650690761006466920238585 53738018070754850190178939)
    ·
      refine ⟨80607027106132275285268409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53738018070754850190178939 80607027106132275285268409)
      ·
        refine ⟨60455270329599206463951307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80607027106132275285268409 60455270329599206463951307)
        ·
          refine ⟨90682905494398809695926961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60455270329599206463951307 90682905494398809695926961)
          ·
            refine ⟨68012179120799107271945221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90682905494398809695926961 68012179120799107271945221)
            ·
              refine ⟨12752283585149832613489729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68012179120799107271945221 12752283585149832613489729)
              ·
                refine ⟨9564212688862374460117297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12752283585149832613489729 9564212688862374460117297)
                ·
                  refine ⟨7173159516646780845087973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9564212688862374460117297 7173159516646780845087973)
                  ·
                    refine ⟨1344967409371271408453995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7173159516646780845087973 1344967409371271408453995)
                    ·
                      rfl

theorem cell22_3928972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_3928972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928972 prefixEnd_3928972 := by exact prefixLift 3928972
  have htrace : WordTrace (prefixWord ++ tailWord_3928972) baseStart_3928972 baseEnd_3928972 := by
    simpa [prefixWord, tailWord_3928972, baseEnd_3928972] using wordTrace_append hprefix tailTrace_3928972
  have hstable : (prefixWord ++ tailWord_3928972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928972).length < 2 ^ (prefixWord ++ tailWord_3928972).sum := by decide
  have hdescent : baseEnd_3928972 < baseStart_3928972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928985 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 2, 7]
def baseStart_3928985 : Nat := 118140960795 + 3928985 * 2 ^ 59
def prefixEnd_3928985 : Nat := 4983230072969 + 3 ^ 40 * 3928985 * 2
def baseEnd_3928985 : Nat := 1344971859536943707878955

theorem tailTrace_3928985 : CollatzResearch.WordTrace tailWord_3928985 prefixEnd_3928985 1344971859536943707878955 := by
  unfold tailWord_3928985
  simp only [CollatzResearch.WordTrace]
  refine ⟨143301855670965837060700409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95534570447310558040466939 143301855670965837060700409)
  ·
    refine ⟨107476391753224377795525307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143301855670965837060700409 107476391753224377795525307)
    ·
      refine ⟨161214587629836566693287961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107476391753224377795525307 161214587629836566693287961)
      ·
        refine ⟨120910940722377425019965971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161214587629836566693287961 120910940722377425019965971)
        ·
          refine ⟨181366411083566137529948957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120910940722377425019965971 181366411083566137529948957)
          ·
            refine ⟨68012404156337301573730859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181366411083566137529948957 68012404156337301573730859)
            ·
              refine ⟨102018606234505952360596289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68012404156337301573730859 102018606234505952360596289)
              ·
                refine ⟨76513954675879464270447217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102018606234505952360596289 76513954675879464270447217)
                ·
                  refine ⟨57385466006909598202835413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76513954675879464270447217 57385466006909598202835413)
                  ·
                    refine ⟨1344971859536943707878955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57385466006909598202835413 1344971859536943707878955)
                    ·
                      rfl

theorem cell22_3928985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_3928985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3928985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3928985 prefixEnd_3928985 := by exact prefixLift 3928985
  have htrace : WordTrace (prefixWord ++ tailWord_3928985) baseStart_3928985 baseEnd_3928985 := by
    simpa [prefixWord, tailWord_3928985, baseEnd_3928985] using wordTrace_append hprefix tailTrace_3928985
  have hstable : (prefixWord ++ tailWord_3928985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928985).length < 2 ^ (prefixWord ++ tailWord_3928985).sum := by decide
  have hdescent : baseEnd_3928985 < baseStart_3928985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929036 : List Nat := [2, 2, 1, 4, 1, 1, 1, 6, 1, 3]
def baseStart_3929036 : Nat := 118140960795 + 3929036 * 2 ^ 59
def prefixEnd_3929036 : Nat := 4983230072969 + 3 ^ 40 * 3929036 * 2
def baseEnd_3929036 : Nat := 1344989317879196574853799

theorem tailTrace_3929036 : CollatzResearch.WordTrace tailWord_3929036 prefixEnd_3929036 1344989317879196574853799 := by
  unfold tailWord_3929036
  simp only [CollatzResearch.WordTrace]
  refine ⟨71651857896890536385403481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95535810529187381847204641 71651857896890536385403481)
  ·
    refine ⟨53738893422667902289052611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71651857896890536385403481 53738893422667902289052611)
    ·
      refine ⟨80608340134001853433578917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53738893422667902289052611 80608340134001853433578917)
      ·
        refine ⟨15114063775125347518796047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80608340134001853433578917 15114063775125347518796047)
        ·
          refine ⟨22671095662688021278194071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15114063775125347518796047 22671095662688021278194071)
          ·
            refine ⟨34006643494032031917291107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22671095662688021278194071 34006643494032031917291107)
            ·
              refine ⟨51009965241048047875936661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34006643494032031917291107 51009965241048047875936661)
              ·
                refine ⟨2391092120674127244184531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51009965241048047875936661 2391092120674127244184531)
                ·
                  refine ⟨3586638181011190866276797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2391092120674127244184531 3586638181011190866276797)
                  ·
                    refine ⟨1344989317879196574853799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3586638181011190866276797 1344989317879196574853799)
                    ·
                      rfl

theorem cell22_3929036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 1, 3].length) (baseStart_3929036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929036 prefixEnd_3929036 := by exact prefixLift 3929036
  have htrace : WordTrace (prefixWord ++ tailWord_3929036) baseStart_3929036 baseEnd_3929036 := by
    simpa [prefixWord, tailWord_3929036, baseEnd_3929036] using wordTrace_append hprefix tailTrace_3929036
  have hstable : (prefixWord ++ tailWord_3929036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929036).length < 2 ^ (prefixWord ++ tailWord_3929036).sum := by decide
  have hdescent : baseEnd_3929036 < baseStart_3929036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929070 : List Nat := [4, 1, 2, 1, 4, 2, 1, 3, 1, 3]
def baseStart_3929070 : Nat := 118140960795 + 3929070 * 2 ^ 59
def prefixEnd_3929070 : Nat := 4983230072969 + 3 ^ 40 * 3929070 * 2
def baseEnd_3929070 : Nat := 1345000956774031819503695

theorem tailTrace_3929070 : CollatzResearch.WordTrace tailWord_3929070 prefixEnd_3929070 1345000956774031819503695 := by
  unfold tailWord_3929070
  simp only [CollatzResearch.WordTrace]
  refine ⟨17913119484457237072193083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95536637250438597718363109 17913119484457237072193083)
  ·
    refine ⟨26869679226685855608289625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17913119484457237072193083 26869679226685855608289625)
    ·
      refine ⟨20152259420014391706217219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26869679226685855608289625 20152259420014391706217219)
      ·
        refine ⟨30228389130021587559325829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20152259420014391706217219 30228389130021587559325829)
        ·
          refine ⟨5667822961879047667373593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30228389130021587559325829 5667822961879047667373593)
          ·
            refine ⟨4250867221409285750530195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5667822961879047667373593 4250867221409285750530195)
            ·
              refine ⟨6376300832113928625795293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4250867221409285750530195 6376300832113928625795293)
              ·
                refine ⟨2391112812042723234673235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6376300832113928625795293 2391112812042723234673235)
                ·
                  refine ⟨3586669218064084852009853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2391112812042723234673235 3586669218064084852009853)
                  ·
                    refine ⟨1345000956774031819503695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3586669218064084852009853 1345000956774031819503695)
                    ·
                      rfl

theorem cell22_3929070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_3929070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929070 prefixEnd_3929070 := by exact prefixLift 3929070
  have htrace : WordTrace (prefixWord ++ tailWord_3929070) baseStart_3929070 baseEnd_3929070 := by
    simpa [prefixWord, tailWord_3929070, baseEnd_3929070] using wordTrace_append hprefix tailTrace_3929070
  have hstable : (prefixWord ++ tailWord_3929070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929070).length < 2 ^ (prefixWord ++ tailWord_3929070).sum := by decide
  have hdescent : baseEnd_3929070 < baseStart_3929070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929107 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 6, 4]
def baseStart_3929107 : Nat := 118140960795 + 3929107 * 2 ^ 59
def prefixEnd_3929107 : Nat := 4983230072969 + 3 ^ 40 * 3929107 * 2
def baseEnd_3929107 : Nat := 1345013622630176056328581

theorem tailTrace_3929107 : CollatzResearch.WordTrace tailWord_3929107 prefixEnd_3929107 1345013622630176056328581 := by
  unfold tailWord_3929107
  simp only [CollatzResearch.WordTrace]
  refine ⟨143306305376523851896641575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95537536917682567931094383 143306305376523851896641575)
  ·
    refine ⟨214959458064785777844962363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143306305376523851896641575 214959458064785777844962363)
    ·
      refine ⟨322439187097178666767443545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214959458064785777844962363 322439187097178666767443545)
      ·
        refine ⟨241829390322884000075582659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322439187097178666767443545 241829390322884000075582659)
        ·
          refine ⟨362744085484326000113373989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241829390322884000075582659 362744085484326000113373989)
          ·
            refine ⟨68014516028311125021257623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 362744085484326000113373989 68014516028311125021257623)
            ·
              refine ⟨102021774042466687531886435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68014516028311125021257623 102021774042466687531886435)
              ·
                refine ⟨153032661063700031297829653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102021774042466687531886435 153032661063700031297829653)
                ·
                  refine ⟨7173405987360938967085765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153032661063700031297829653 7173405987360938967085765)
                  ·
                    refine ⟨1345013622630176056328581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7173405987360938967085765 1345013622630176056328581)
                    ·
                      rfl

theorem cell22_3929107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 4].length) (baseStart_3929107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929107 prefixEnd_3929107 := by exact prefixLift 3929107
  have htrace : WordTrace (prefixWord ++ tailWord_3929107) baseStart_3929107 baseEnd_3929107 := by
    simpa [prefixWord, tailWord_3929107, baseEnd_3929107] using wordTrace_append hprefix tailTrace_3929107
  have hstable : (prefixWord ++ tailWord_3929107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929107).length < 2 ^ (prefixWord ++ tailWord_3929107).sum := by decide
  have hdescent : baseEnd_3929107 < baseStart_3929107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929152 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 1, 8]
def baseStart_3929152 : Nat := 118140960795 + 3929152 * 2 ^ 59
def prefixEnd_3929152 : Nat := 4983230072969 + 3 ^ 40 * 3929152 * 2
def baseEnd_3929152 : Nat := 1345029027049810938953443

theorem tailTrace_3929152 : CollatzResearch.WordTrace tailWord_3929152 prefixEnd_3929152 1345029027049810938953443 := by
  unfold tailWord_3929152
  simp only [CollatzResearch.WordTrace]
  refine ⟨71653973330680412291014855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95538631107573883054686473 71653973330680412291014855)
  ·
    refine ⟨107480959996020618436522283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71653973330680412291014855 107480959996020618436522283)
    ·
      refine ⟨161221439994030927654783425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107480959996020618436522283 161221439994030927654783425)
      ·
        refine ⟨120916079995523195741087569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161221439994030927654783425 120916079995523195741087569)
        ·
          refine ⟨90687059996642396805815677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120916079995523195741087569 90687059996642396805815677)
          ·
            refine ⟨34007647498740898802180879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90687059996642396805815677 34007647498740898802180879)
            ·
              refine ⟨51011471248111348203271319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34007647498740898802180879 51011471248111348203271319)
              ·
                refine ⟨76517206872167022304906979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51011471248111348203271319 76517206872167022304906979)
                ·
                  refine ⟨114775810308250533457360469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76517206872167022304906979 114775810308250533457360469)
                  ·
                    refine ⟨1345029027049810938953443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114775810308250533457360469 1345029027049810938953443)
                    ·
                      rfl

theorem cell22_3929152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_3929152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929152 prefixEnd_3929152 := by exact prefixLift 3929152
  have htrace : WordTrace (prefixWord ++ tailWord_3929152) baseStart_3929152 baseEnd_3929152 := by
    simpa [prefixWord, tailWord_3929152, baseEnd_3929152] using wordTrace_append hprefix tailTrace_3929152
  have hstable : (prefixWord ++ tailWord_3929152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929152).length < 2 ^ (prefixWord ++ tailWord_3929152).sum := by decide
  have hdescent : baseEnd_3929152 < baseStart_3929152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929205 : List Nat := [1, 3, 4, 3, 1, 1, 2, 1, 3, 3]
def baseStart_3929205 : Nat := 118140960795 + 3929205 * 2 ^ 59
def prefixEnd_3929205 : Nat := 4983230072969 + 3 ^ 40 * 3929205 * 2
def baseEnd_3929205 : Nat := 1345047170032936467378281

theorem tailTrace_3929205 : CollatzResearch.WordTrace tailWord_3929205 prefixEnd_3929205 1345047170032936467378281 := by
  unfold tailWord_3929205
  simp only [CollatzResearch.WordTrace]
  refine ⟨143309879730168814633709069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95539919820112543089139379 143309879730168814633709069)
  ·
    refine ⟨53741204898813305487640901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143309879730168814633709069 53741204898813305487640901)
    ·
      refine ⟨10076475918527494778932669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53741204898813305487640901 10076475918527494778932669)
      ·
        refine ⟨3778678469447810542099751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10076475918527494778932669 3778678469447810542099751)
        ·
          refine ⟨5668017704171715813149627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3778678469447810542099751 5668017704171715813149627)
          ·
            refine ⟨8502026556257573719724441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5668017704171715813149627 8502026556257573719724441)
            ·
              refine ⟨6376519917193180289793331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8502026556257573719724441 6376519917193180289793331)
              ·
                refine ⟨9564779875789770434689997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6376519917193180289793331 9564779875789770434689997)
                ·
                  refine ⟨3586792453421163913008749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9564779875789770434689997 3586792453421163913008749)
                  ·
                    refine ⟨1345047170032936467378281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3586792453421163913008749 1345047170032936467378281)
                    ·
                      rfl

theorem cell22_3929205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_3929205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929205 prefixEnd_3929205 := by exact prefixLift 3929205
  have htrace : WordTrace (prefixWord ++ tailWord_3929205) baseStart_3929205 baseEnd_3929205 := by
    simpa [prefixWord, tailWord_3929205, baseEnd_3929205] using wordTrace_append hprefix tailTrace_3929205
  have hstable : (prefixWord ++ tailWord_3929205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929205).length < 2 ^ (prefixWord ++ tailWord_3929205).sum := by decide
  have hdescent : baseEnd_3929205 < baseStart_3929205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929381 : List Nat := [1, 3, 1, 2, 4, 1, 1, 3, 6]
def baseStart_3929381 : Nat := 118140960795 + 3929381 * 2 ^ 59
def prefixEnd_3929381 : Nat := 4983230072969 + 3 ^ 40 * 3929381 * 2
def baseEnd_3929381 : Nat := 448369139476576891659247

theorem tailTrace_3929381 : CollatzResearch.WordTrace tailWord_3929381 prefixEnd_3929381 448369139476576891659247 := by
  unfold tailWord_3929381
  simp only [CollatzResearch.WordTrace]
  refine ⟨143316298977531196692115997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95544199318354131128077331 143316298977531196692115997)
  ·
    refine ⟨53743612116574198759543499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143316298977531196692115997 53743612116574198759543499)
    ·
      refine ⟨80615418174861298139315249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53743612116574198759543499 80615418174861298139315249)
      ·
        refine ⟨60461563631145973604486437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80615418174861298139315249 60461563631145973604486437)
        ·
          refine ⟨11336543180839870050841207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60461563631145973604486437 11336543180839870050841207)
          ·
            refine ⟨17004814771259805076261811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11336543180839870050841207 17004814771259805076261811)
            ·
              refine ⟨25507222156889707614392717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17004814771259805076261811 25507222156889707614392717)
              ·
                refine ⟨9565208308833640355397269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25507222156889707614392717 9565208308833640355397269)
                ·
                  refine ⟨448369139476576891659247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9565208308833640355397269 448369139476576891659247)
                  ·
                    rfl

theorem cell22_3929381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_3929381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929381 prefixEnd_3929381 := by exact prefixLift 3929381
  have htrace : WordTrace (prefixWord ++ tailWord_3929381) baseStart_3929381 baseEnd_3929381 := by
    simpa [prefixWord, tailWord_3929381, baseEnd_3929381] using wordTrace_append hprefix tailTrace_3929381
  have hstable : (prefixWord ++ tailWord_3929381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929381).length < 2 ^ (prefixWord ++ tailWord_3929381).sum := by decide
  have hdescent : baseEnd_3929381 < baseStart_3929381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929411 : List Nat := [1, 1, 1, 3, 1, 3, 1, 5, 2, 4]
def baseStart_3929411 : Nat := 118140960795 + 3929411 * 2 ^ 59
def prefixEnd_3929411 : Nat := 4983230072969 + 3 ^ 40 * 3929411 * 2
def baseEnd_3929411 : Nat := 1345117688042820596727649

theorem tailTrace_3929411 : CollatzResearch.WordTrace tailWord_3929411 prefixEnd_3929411 1345117688042820596727649 := by
  unfold tailWord_3929411
  simp only [CollatzResearch.WordTrace]
  refine ⟨143317393167422511815708087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95544928778281674543805391 143317393167422511815708087)
  ·
    refine ⟨214976089751133767723562131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143317393167422511815708087 214976089751133767723562131)
    ·
      refine ⟨322464134626700651585343197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214976089751133767723562131 322464134626700651585343197)
      ·
        refine ⟨120924050485012744344503699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322464134626700651585343197 120924050485012744344503699)
        ·
          refine ⟨181386075727519116516755549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120924050485012744344503699 181386075727519116516755549)
          ·
            refine ⟨68019778397819668693783331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181386075727519116516755549 68019778397819668693783331)
            ·
              refine ⟨102029667596729503040674997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68019778397819668693783331 102029667596729503040674997)
              ·
                refine ⟨9565281337193390910063281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102029667596729503040674997 9565281337193390910063281)
                ·
                  refine ⟨7173961002895043182547461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9565281337193390910063281 7173961002895043182547461)
                  ·
                    refine ⟨1345117688042820596727649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7173961002895043182547461 1345117688042820596727649)
                    ·
                      rfl

theorem cell22_3929411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 4].length) (baseStart_3929411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929411 prefixEnd_3929411 := by exact prefixLift 3929411
  have htrace : WordTrace (prefixWord ++ tailWord_3929411) baseStart_3929411 baseEnd_3929411 := by
    simpa [prefixWord, tailWord_3929411, baseEnd_3929411] using wordTrace_append hprefix tailTrace_3929411
  have hstable : (prefixWord ++ tailWord_3929411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929411).length < 2 ^ (prefixWord ++ tailWord_3929411).sum := by decide
  have hdescent : baseEnd_3929411 < baseStart_3929411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929415 : List Nat := [1, 1, 4, 1, 2, 5, 1, 3, 4]
def baseStart_3929415 : Nat := 118140960795 + 3929415 * 2 ^ 59
def prefixEnd_3929415 : Nat := 4983230072969 + 3 ^ 40 * 3929415 * 2
def baseEnd_3929415 : Nat := 448373019108188639875879

theorem tailTrace_3929415 : CollatzResearch.WordTrace tailWord_3929415 prefixEnd_3929415 448373019108188639875879 := by
  unfold tailWord_3929415
  simp only [CollatzResearch.WordTrace]
  refine ⟨143317539059408020498853699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95545026039605346999235799 143317539059408020498853699)
  ·
    refine ⟨214976308589112030748280549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143317539059408020498853699 214976308589112030748280549)
    ·
      refine ⟨40308057860458505765302603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214976308589112030748280549 40308057860458505765302603)
      ·
        refine ⟨60462086790687758647953905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40308057860458505765302603 60462086790687758647953905)
        ·
          refine ⟨45346565093015818985965429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60462086790687758647953905 45346565093015818985965429)
          ·
            refine ⟨4251240477470233029934259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45346565093015818985965429 4251240477470233029934259)
            ·
              refine ⟨6376860716205349544901389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4251240477470233029934259 6376860716205349544901389)
              ·
                refine ⟨2391322768577006079338021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6376860716205349544901389 2391322768577006079338021)
                ·
                  refine ⟨448373019108188639875879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2391322768577006079338021 448373019108188639875879)
                  ·
                    rfl

theorem cell22_3929415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 4].length) (baseStart_3929415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929415 prefixEnd_3929415 := by exact prefixLift 3929415
  have htrace : WordTrace (prefixWord ++ tailWord_3929415) baseStart_3929415 baseEnd_3929415 := by
    simpa [prefixWord, tailWord_3929415, baseEnd_3929415] using wordTrace_append hprefix tailTrace_3929415
  have hstable : (prefixWord ++ tailWord_3929415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929415).length < 2 ^ (prefixWord ++ tailWord_3929415).sum := by decide
  have hdescent : baseEnd_3929415 < baseStart_3929415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929428 : List Nat := [2, 4, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_3929428 : Nat := 118140960795 + 3929428 * 2 ^ 59
def prefixEnd_3929428 : Nat := 4983230072969 + 3 ^ 40 * 3929428 * 2
def baseEnd_3929428 : Nat := 1345123507490238219052597

theorem tailTrace_3929428 : CollatzResearch.WordTrace tailWord_3929428 prefixEnd_3929428 1345123507490238219052597 := by
  unfold tailWord_3929428
  simp only [CollatzResearch.WordTrace]
  refine ⟨71659006604180461859538469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95545342138907282479384625 71659006604180461859538469)
  ·
    refine ⟨13436063738283836598663463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71659006604180461859538469 13436063738283836598663463)
    ·
      refine ⟨20154095607425754897995195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13436063738283836598663463 20154095607425754897995195)
      ·
        refine ⟨30231143411138632346992793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20154095607425754897995195 30231143411138632346992793)
        ·
          refine ⟨22673357558353974260244595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30231143411138632346992793 22673357558353974260244595)
          ·
            refine ⟨34010036337530961390366893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22673357558353974260244595 34010036337530961390366893)
            ·
              refine ⟨12753763626574110521387585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34010036337530961390366893 12753763626574110521387585)
              ·
                refine ⟨9565322719930582891040689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12753763626574110521387585 9565322719930582891040689)
                ·
                  refine ⟨7173992039947937168280517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9565322719930582891040689 7173992039947937168280517)
                  ·
                    refine ⟨1345123507490238219052597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7173992039947937168280517 1345123507490238219052597)
                    ·
                      rfl

theorem cell22_3929428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_3929428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929428 prefixEnd_3929428 := by exact prefixLift 3929428
  have htrace : WordTrace (prefixWord ++ tailWord_3929428) baseStart_3929428 baseEnd_3929428 := by
    simpa [prefixWord, tailWord_3929428, baseEnd_3929428] using wordTrace_append hprefix tailTrace_3929428
  have hstable : (prefixWord ++ tailWord_3929428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929428).length < 2 ^ (prefixWord ++ tailWord_3929428).sum := by decide
  have hdescent : baseEnd_3929428 < baseStart_3929428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929458 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 5, 3]
def baseStart_3929458 : Nat := 118140960795 + 3929458 * 2 ^ 59
def prefixEnd_3929458 : Nat := 4983230072969 + 3 ^ 40 * 3929458 * 2
def baseEnd_3929458 : Nat := 1345133777103328140802505

theorem tailTrace_3929458 : CollatzResearch.WordTrace tailWord_3929458 prefixEnd_3929458 1345133777103328140802505 := by
  unfold tailWord_3929458
  simp only [CollatzResearch.WordTrace]
  refine ⟨35829776849563059710667257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95546071598834825895112685 35829776849563059710667257)
  ·
    refine ⟨26872332637172294783000443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35829776849563059710667257 26872332637172294783000443)
    ·
      refine ⟨40308498955758442174500665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26872332637172294783000443 40308498955758442174500665)
      ·
        refine ⟨30231374216818831630875499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40308498955758442174500665 30231374216818831630875499)
        ·
          refine ⟨45347061325228247446313249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30231374216818831630875499 45347061325228247446313249)
          ·
            refine ⟨34010295993921185584734937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45347061325228247446313249 34010295993921185584734937)
            ·
              refine ⟨25507721995440889188551203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34010295993921185584734937 25507721995440889188551203)
              ·
                refine ⟨38261582993161333782826805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25507721995440889188551203 38261582993161333782826805)
                ·
                  refine ⟨3587023405608875042140013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38261582993161333782826805 3587023405608875042140013)
                  ·
                    refine ⟨1345133777103328140802505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3587023405608875042140013 1345133777103328140802505)
                    ·
                      rfl

theorem cell22_3929458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_3929458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929458 prefixEnd_3929458 := by exact prefixLift 3929458
  have htrace : WordTrace (prefixWord ++ tailWord_3929458) baseStart_3929458 baseEnd_3929458 := by
    simpa [prefixWord, tailWord_3929458, baseEnd_3929458] using wordTrace_append hprefix tailTrace_3929458
  have hstable : (prefixWord ++ tailWord_3929458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929458).length < 2 ^ (prefixWord ++ tailWord_3929458).sum := by decide
  have hdescent : baseEnd_3929458 < baseStart_3929458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929503 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 2, 5]
def baseStart_3929503 : Nat := 118140960795 + 3929503 * 2 ^ 59
def prefixEnd_3929503 : Nat := 4983230072969 + 3 ^ 40 * 3929503 * 2
def baseEnd_3929503 : Nat := 1345149181522963023427367

theorem tailTrace_3929503 : CollatzResearch.WordTrace tailWord_3929503 prefixEnd_3929503 1345149181522963023427367 := by
  unfold tailWord_3929503
  simp only [CollatzResearch.WordTrace]
  refine ⟨143320748683089211528057163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95547165788726141018704775 143320748683089211528057163)
  ·
    refine ⟨214981123024633817292085745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143320748683089211528057163 214981123024633817292085745)
    ·
      refine ⟨161235842268475362969064309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214981123024633817292085745 161235842268475362969064309)
      ·
        refine ⟨15115860212669565278349779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161235842268475362969064309 15115860212669565278349779)
        ·
          refine ⟨22673790319004347917524669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15115860212669565278349779 22673790319004347917524669)
          ·
            refine ⟨8502671369626630469071751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22673790319004347917524669 8502671369626630469071751)
            ·
              refine ⟨12754007054439945703607627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8502671369626630469071751 12754007054439945703607627)
              ·
                refine ⟨19131010581659918555411441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12754007054439945703607627 19131010581659918555411441)
                ·
                  refine ⟨14348257936244938916558581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19131010581659918555411441 14348257936244938916558581)
                  ·
                    refine ⟨1345149181522963023427367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14348257936244938916558581 1345149181522963023427367)
                    ·
                      rfl

theorem cell22_3929503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_3929503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929503 prefixEnd_3929503 := by exact prefixLift 3929503
  have htrace : WordTrace (prefixWord ++ tailWord_3929503) baseStart_3929503 baseEnd_3929503 := by
    simpa [prefixWord, tailWord_3929503, baseEnd_3929503] using wordTrace_append hprefix tailTrace_3929503
  have hstable : (prefixWord ++ tailWord_3929503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929503).length < 2 ^ (prefixWord ++ tailWord_3929503).sum := by decide
  have hdescent : baseEnd_3929503 < baseStart_3929503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929516 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 8]
def baseStart_3929516 : Nat := 118140960795 + 3929516 * 2 ^ 59
def prefixEnd_3929516 : Nat := 4983230072969 + 3 ^ 40 * 3929516 * 2
def baseEnd_3929516 : Nat := 448384543896211774284109

theorem tailTrace_3929516 : CollatzResearch.WordTrace tailWord_3929516 prefixEnd_3929516 448384543896211774284109 := by
  unfold tailWord_3929516
  simp only [CollatzResearch.WordTrace]
  refine ⟨71660611416021057374140201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95547481888028076498853601 71660611416021057374140201)
  ·
    refine ⟨53745458562015793030605151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71660611416021057374140201 53745458562015793030605151)
    ·
      refine ⟨80618187843023689545907727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53745458562015793030605151 80618187843023689545907727)
      ·
        refine ⟨120927281764535534318861591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80618187843023689545907727 120927281764535534318861591)
        ·
          refine ⟨181390922646803301478292387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120927281764535534318861591 181390922646803301478292387)
          ·
            refine ⟨272086383970204952217438581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181390922646803301478292387 272086383970204952217438581)
            ·
              refine ⟨25508098497206714270384867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 272086383970204952217438581 25508098497206714270384867)
              ·
                refine ⟨38262147745810071405577301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25508098497206714270384867 38262147745810071405577301)
                ·
                  refine ⟨448384543896211774284109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38262147745810071405577301 448384543896211774284109)
                  ·
                    rfl

theorem cell22_3929516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_3929516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929516 prefixEnd_3929516 := by exact prefixLift 3929516
  have htrace : WordTrace (prefixWord ++ tailWord_3929516) baseStart_3929516 baseEnd_3929516 := by
    simpa [prefixWord, tailWord_3929516, baseEnd_3929516] using wordTrace_append hprefix tailTrace_3929516
  have hstable : (prefixWord ++ tailWord_3929516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929516).length < 2 ^ (prefixWord ++ tailWord_3929516).sum := by decide
  have hdescent : baseEnd_3929516 < baseStart_3929516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929550 : List Nat := [4, 1, 1, 1, 2, 1, 4, 4, 4]
def baseStart_3929550 : Nat := 118140960795 + 3929550 * 2 ^ 59
def prefixEnd_3929550 : Nat := 4983230072969 + 3 ^ 40 * 3929550 * 2
def baseEnd_3929550 : Nat := 448388423527823522500741

theorem tailTrace_3929550 : CollatzResearch.WordTrace tailWord_3929550 prefixEnd_3929550 448388423527823522500741 := by
  unfold tailWord_3929550
  simp only [CollatzResearch.WordTrace]
  refine ⟨17915307864239867319377263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95548308609279292370012069 17915307864239867319377263)
  ·
    refine ⟨26872961796359800979065895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17915307864239867319377263 26872961796359800979065895)
    ·
      refine ⟨40309442694539701468598843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26872961796359800979065895 40309442694539701468598843)
      ·
        refine ⟨60464164041809552202898265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40309442694539701468598843 60464164041809552202898265)
        ·
          refine ⟨45348123031357164152173699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60464164041809552202898265 45348123031357164152173699)
          ·
            refine ⟨68022184547035746228260549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45348123031357164152173699 68022184547035746228260549)
            ·
              refine ⟨12754159602569202417798853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68022184547035746228260549 12754159602569202417798853)
              ·
                refine ⟨2391404925481725453337285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12754159602569202417798853 2391404925481725453337285)
                ·
                  refine ⟨448388423527823522500741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2391404925481725453337285 448388423527823522500741)
                  ·
                    rfl

theorem cell22_3929550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_3929550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929550 prefixEnd_3929550 := by exact prefixLift 3929550
  have htrace : WordTrace (prefixWord ++ tailWord_3929550) baseStart_3929550 baseEnd_3929550 := by
    simpa [prefixWord, tailWord_3929550, baseEnd_3929550] using wordTrace_append hprefix tailTrace_3929550
  have hstable : (prefixWord ++ tailWord_3929550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929550).length < 2 ^ (prefixWord ++ tailWord_3929550).sum := by decide
  have hdescent : baseEnd_3929550 < baseStart_3929550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929565 : List Nat := [1, 4, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3929565 : Nat := 118140960795 + 3929565 * 2 ^ 59
def prefixEnd_3929565 : Nat := 4983230072969 + 3 ^ 40 * 3929565 * 2
def baseEnd_3929565 : Nat := 1345170405390015528377177

theorem tailTrace_3929565 : CollatzResearch.WordTrace tailWord_3929565 prefixEnd_3929565 1345170405390015528377177 := by
  unfold tailWord_3929565
  simp only [CollatzResearch.WordTrace]
  refine ⟨143323010008864596116814149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95548673339243064077876099 143323010008864596116814149)
  ·
    refine ⟨26873064376662111771902653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143323010008864596116814149 26873064376662111771902653)
    ·
      refine ⟨10077399141248291914463495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26873064376662111771902653 10077399141248291914463495)
      ·
        refine ⟨15116098711872437871695243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10077399141248291914463495 15116098711872437871695243)
        ·
          refine ⟨22674148067808656807542865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15116098711872437871695243 22674148067808656807542865)
          ·
            refine ⟨17005611050856492605657149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22674148067808656807542865 17005611050856492605657149)
            ·
              refine ⟨6377104144071184727121431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17005611050856492605657149 6377104144071184727121431)
              ·
                refine ⟨9565656216106777090682147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6377104144071184727121431 9565656216106777090682147)
                ·
                  refine ⟨14348484324160165636023221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9565656216106777090682147 14348484324160165636023221)
                  ·
                    refine ⟨1345170405390015528377177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14348484324160165636023221 1345170405390015528377177)
                    ·
                      rfl

theorem cell22_3929565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3929565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929565 prefixEnd_3929565 := by exact prefixLift 3929565
  have htrace : WordTrace (prefixWord ++ tailWord_3929565) baseStart_3929565 baseEnd_3929565 := by
    simpa [prefixWord, tailWord_3929565, baseEnd_3929565] using wordTrace_append hprefix tailTrace_3929565
  have hstable : (prefixWord ++ tailWord_3929565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929565).length < 2 ^ (prefixWord ++ tailWord_3929565).sum := by decide
  have hdescent : baseEnd_3929565 < baseStart_3929565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929700 : List Nat := [2, 3, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_3929700 : Nat := 118140960795 + 3929700 * 2 ^ 59
def prefixEnd_3929700 : Nat := 4983230072969 + 3 ^ 40 * 3929700 * 2
def baseEnd_3929700 : Nat := 1345216618648920176251763

theorem tailTrace_3929700 : CollatzResearch.WordTrace tailWord_3929700 prefixEnd_3929700 1345216618648920176251763 := by
  unfold tailWord_3929700
  simp only [CollatzResearch.WordTrace]
  refine ⟨71663966931687757086489277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95551955908917009448652369 71663966931687757086489277)
  ·
    refine ⟨26873987599382908907433479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71663966931687757086489277 26873987599382908907433479)
    ·
      refine ⟨40310981399074363361150219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26873987599382908907433479 40310981399074363361150219)
      ·
        refine ⟨60466472098611545041725329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40310981399074363361150219 60466472098611545041725329)
        ·
          refine ⟨45349854073958658781293997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60466472098611545041725329 45349854073958658781293997)
          ·
            refine ⟨17006195277734497042985249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45349854073958658781293997 17006195277734497042985249)
            ·
              refine ⟨12754646458300872782238937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17006195277734497042985249 12754646458300872782238937)
              ·
                refine ⟨9565984843725654586679203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12754646458300872782238937 9565984843725654586679203)
                ·
                  refine ⟨14348977265588481880018805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9565984843725654586679203 14348977265588481880018805)
                  ·
                    refine ⟨1345216618648920176251763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14348977265588481880018805 1345216618648920176251763)
                    ·
                      rfl

theorem cell22_3929700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_3929700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929700 prefixEnd_3929700 := by exact prefixLift 3929700
  have htrace : WordTrace (prefixWord ++ tailWord_3929700) baseStart_3929700 baseEnd_3929700 := by
    simpa [prefixWord, tailWord_3929700, baseEnd_3929700] using wordTrace_append hprefix tailTrace_3929700
  have hstable : (prefixWord ++ tailWord_3929700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929700).length < 2 ^ (prefixWord ++ tailWord_3929700).sum := by decide
  have hdescent : baseEnd_3929700 < baseStart_3929700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929704 : List Nat := [2, 1, 4, 3, 1, 1, 4, 1, 1, 4]
def baseStart_3929704 : Nat := 118140960795 + 3929704 * 2 ^ 59
def prefixEnd_3929704 : Nat := 4983230072969 + 3 ^ 40 * 3929704 * 2
def baseEnd_3929704 : Nat := 1345217987930665499151751

theorem tailTrace_3929704 : CollatzResearch.WordTrace tailWord_3929704 prefixEnd_3929704 1345217987930665499151751 := by
  unfold tailWord_3929704
  simp only [CollatzResearch.WordTrace]
  refine ⟨71664039877680511428062083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95552053170240681904082777 71664039877680511428062083)
  ·
    refine ⟨107496059816520767142093125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71664039877680511428062083 107496059816520767142093125)
    ·
      refine ⟨20155511215597643839142461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107496059816520767142093125 20155511215597643839142461)
      ·
        refine ⟨7558316705849116439678423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20155511215597643839142461 7558316705849116439678423)
        ·
          refine ⟨11337475058773674659517635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7558316705849116439678423 11337475058773674659517635)
          ·
            refine ⟨17006212588160511989276453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11337475058773674659517635 17006212588160511989276453)
            ·
              refine ⟨3188664860280095997989335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17006212588160511989276453 3188664860280095997989335)
              ·
                refine ⟨4782997290420143996984003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3188664860280095997989335 4782997290420143996984003)
                ·
                  refine ⟨7174495935630215995476005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4782997290420143996984003 7174495935630215995476005)
                  ·
                    refine ⟨1345217987930665499151751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7174495935630215995476005 1345217987930665499151751)
                    ·
                      rfl

theorem cell22_3929704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_3929704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929704 prefixEnd_3929704 := by exact prefixLift 3929704
  have htrace : WordTrace (prefixWord ++ tailWord_3929704) baseStart_3929704 baseEnd_3929704 := by
    simpa [prefixWord, tailWord_3929704, baseEnd_3929704] using wordTrace_append hprefix tailTrace_3929704
  have hstable : (prefixWord ++ tailWord_3929704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929704).length < 2 ^ (prefixWord ++ tailWord_3929704).sum := by decide
  have hdescent : baseEnd_3929704 < baseStart_3929704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929745 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 5, 3]
def baseStart_3929745 : Nat := 118140960795 + 3929745 * 2 ^ 59
def prefixEnd_3929745 : Nat := 4983230072969 + 3 ^ 40 * 3929745 * 2
def baseEnd_3929745 : Nat := 1345232023068555058876625

theorem tailTrace_3929745 : CollatzResearch.WordTrace tailWord_3929745 prefixEnd_3929745 1345232023068555058876625 := by
  unfold tailWord_3929745
  simp only [CollatzResearch.WordTrace]
  refine ⟨143329575148212486858366689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95553050098808324572244459 143329575148212486858366689)
  ·
    refine ⟨107497181361159365143775017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143329575148212486858366689 107497181361159365143775017)
    ·
      refine ⟨80622886020869523857831263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107497181361159365143775017 80622886020869523857831263)
      ·
        refine ⟨120934329031304285786746895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80622886020869523857831263 120934329031304285786746895)
        ·
          refine ⟨181401493546956428680120343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120934329031304285786746895 181401493546956428680120343)
          ·
            refine ⟨272102240320434643020180515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181401493546956428680120343 272102240320434643020180515)
            ·
              refine ⟨408153360480651964530270773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272102240320434643020180515 408153360480651964530270773)
              ·
                refine ⟨38264377545061121674712885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 408153360480651964530270773 38264377545061121674712885)
                ·
                  refine ⟨3587285394849480157004333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38264377545061121674712885 3587285394849480157004333)
                  ·
                    refine ⟨1345232023068555058876625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3587285394849480157004333 1345232023068555058876625)
                    ·
                      rfl

theorem cell22_3929745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_3929745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929745 prefixEnd_3929745 := by exact prefixLift 3929745
  have htrace : WordTrace (prefixWord ++ tailWord_3929745) baseStart_3929745 baseEnd_3929745 := by
    simpa [prefixWord, tailWord_3929745, baseEnd_3929745] using wordTrace_append hprefix tailTrace_3929745
  have hstable : (prefixWord ++ tailWord_3929745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929745).length < 2 ^ (prefixWord ++ tailWord_3929745).sum := by decide
  have hdescent : baseEnd_3929745 < baseStart_3929745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929775 : List Nat := [1, 1, 2, 1, 2, 4, 2, 4, 5]
def baseStart_3929775 : Nat := 118140960795 + 3929775 * 2 ^ 59
def prefixEnd_3929775 : Nat := 4983230072969 + 3 ^ 40 * 3929775 * 2
def baseEnd_3929775 : Nat := 448414097560548326875511

theorem tailTrace_3929775 : CollatzResearch.WordTrace tailWord_3929775 prefixEnd_3929775 448414097560548326875511 := by
  unfold tailWord_3929775
  simp only [CollatzResearch.WordTrace]
  refine ⟨143330669338103801981958779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95553779558735867987972519 143330669338103801981958779)
  ·
    refine ⟨214996004007155702972938169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143330669338103801981958779 214996004007155702972938169)
    ·
      refine ⟨161247003005366777229703627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214996004007155702972938169 161247003005366777229703627)
      ·
        refine ⟨241870504508050165844555441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161247003005366777229703627 241870504508050165844555441)
        ·
          refine ⟨181402878381037624383416581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241870504508050165844555441 181402878381037624383416581)
          ·
            refine ⟨34013039696444554571890609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181402878381037624383416581 34013039696444554571890609)
            ·
              refine ⟨25509779772333415928917957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34013039696444554571890609 25509779772333415928917957)
              ·
                refine ⟨4783083707312515486672117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25509779772333415928917957 4783083707312515486672117)
                ·
                  refine ⟨448414097560548326875511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4783083707312515486672117 448414097560548326875511)
                  ·
                    rfl

theorem cell22_3929775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 5].length) (baseStart_3929775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929775 prefixEnd_3929775 := by exact prefixLift 3929775
  have htrace : WordTrace (prefixWord ++ tailWord_3929775) baseStart_3929775 baseEnd_3929775 := by
    simpa [prefixWord, tailWord_3929775, baseEnd_3929775] using wordTrace_append hprefix tailTrace_3929775
  have hstable : (prefixWord ++ tailWord_3929775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929775).length < 2 ^ (prefixWord ++ tailWord_3929775).sum := by decide
  have hdescent : baseEnd_3929775 < baseStart_3929775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929850 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 1, 6]
def baseStart_3929850 : Nat := 118140960795 + 3929850 * 2 ^ 59
def prefixEnd_3929850 : Nat := 4983230072969 + 3 ^ 40 * 3929850 * 2
def baseEnd_3929850 : Nat := 1345267966714369785001303

theorem tailTrace_3929850 : CollatzResearch.WordTrace tailWord_3929850 prefixEnd_3929850 1345267966714369785001303 := by
  unfold tailWord_3929850
  simp only [CollatzResearch.WordTrace]
  refine ⟨35833351203208022447734751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95555603208554726527292669 35833351203208022447734751)
  ·
    refine ⟨53750026804812033671602127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35833351203208022447734751 53750026804812033671602127)
    ·
      refine ⟨80625040207218050507403191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53750026804812033671602127 80625040207218050507403191)
      ·
        refine ⟨120937560310827075761104787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80625040207218050507403191 120937560310827075761104787)
        ·
          refine ⟨181406340466240613641657181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120937560310827075761104787 181406340466240613641657181)
          ·
            refine ⟨68027377674840230115621443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181406340466240613641657181 68027377674840230115621443)
            ·
              refine ⟨102041066512260345173432165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68027377674840230115621443 102041066512260345173432165)
              ·
                refine ⟨19132699971048814720018531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102041066512260345173432165 19132699971048814720018531)
                ·
                  refine ⟨28699049956573222080027797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19132699971048814720018531 28699049956573222080027797)
                  ·
                    refine ⟨1345267966714369785001303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28699049956573222080027797 1345267966714369785001303)
                    ·
                      rfl

theorem cell22_3929850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_3929850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929850 prefixEnd_3929850 := by exact prefixLift 3929850
  have htrace : WordTrace (prefixWord ++ tailWord_3929850) baseStart_3929850 baseEnd_3929850 := by
    simpa [prefixWord, tailWord_3929850, baseEnd_3929850] using wordTrace_append hprefix tailTrace_3929850
  have hstable : (prefixWord ++ tailWord_3929850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929850).length < 2 ^ (prefixWord ++ tailWord_3929850).sum := by decide
  have hdescent : baseEnd_3929850 < baseStart_3929850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929852 : List Nat := [2, 2, 2, 1, 3, 1, 4, 1, 1, 5]
def baseStart_3929852 : Nat := 118140960795 + 3929852 * 2 ^ 59
def prefixEnd_3929852 : Nat := 4983230072969 + 3 ^ 40 * 3929852 * 2
def baseEnd_3929852 : Nat := 1345268651355242446451297

theorem tailTrace_3929852 : CollatzResearch.WordTrace tailWord_3929852 prefixEnd_3929852 1345268651355242446451297 := by
  unfold tailWord_3929852
  simp only [CollatzResearch.WordTrace]
  refine ⟨71666738879412422066255905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95555651839216562755007873 71666738879412422066255905)
  ·
    refine ⟨53750054159559316549691929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71666738879412422066255905 53750054159559316549691929)
    ·
      refine ⟨40312540619669487412268947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53750054159559316549691929 40312540619669487412268947)
      ·
        refine ⟨60468810929504231118403421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40312540619669487412268947 60468810929504231118403421)
        ·
          refine ⟨22675804098564086669401283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60468810929504231118403421 22675804098564086669401283)
          ·
            refine ⟨34013706147846130004101925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22675804098564086669401283 34013706147846130004101925)
            ·
              refine ⟨6377569902721149375769111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34013706147846130004101925 6377569902721149375769111)
              ·
                refine ⟨9566354854081724063653667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6377569902721149375769111 9566354854081724063653667)
                ·
                  refine ⟨14349532281122586095480501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9566354854081724063653667 14349532281122586095480501)
                  ·
                    refine ⟨1345268651355242446451297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14349532281122586095480501 1345268651355242446451297)
                    ·
                      rfl

theorem cell22_3929852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_3929852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929852 prefixEnd_3929852 := by exact prefixLift 3929852
  have htrace : WordTrace (prefixWord ++ tailWord_3929852) baseStart_3929852 baseEnd_3929852 := by
    simpa [prefixWord, tailWord_3929852, baseEnd_3929852] using wordTrace_append hprefix tailTrace_3929852
  have hstable : (prefixWord ++ tailWord_3929852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929852).length < 2 ^ (prefixWord ++ tailWord_3929852).sum := by decide
  have hdescent : baseEnd_3929852 < baseStart_3929852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929854 : List Nat := [4, 2, 2, 1, 3, 1, 1, 2, 6]
def baseStart_3929854 : Nat := 118140960795 + 3929854 * 2 ^ 59
def prefixEnd_3929854 : Nat := 4983230072969 + 3 ^ 40 * 3929854 * 2
def baseEnd_3929854 : Nat := 448423111998705035967097

theorem tailTrace_3929854 : CollatzResearch.WordTrace tailWord_3929854 prefixEnd_3929854 448423111998705035967097 := by
  unfold tailWord_3929854
  simp only [CollatzResearch.WordTrace]
  refine ⟨17916693838102199809260577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95555700469878398982723077 17916693838102199809260577)
  ·
    refine ⟨13437520378576649856945433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17916693838102199809260577 13437520378576649856945433)
    ·
      refine ⟨10078140283932487392709075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13437520378576649856945433 10078140283932487392709075)
      ·
        refine ⟨15117210425898731089063613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10078140283932487392709075 15117210425898731089063613)
        ·
          refine ⟨5668953909712024158398855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15117210425898731089063613 5668953909712024158398855)
          ·
            refine ⟨8503430864568036237598283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5668953909712024158398855 8503430864568036237598283)
            ·
              refine ⟨12755146296852054356397425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8503430864568036237598283 12755146296852054356397425)
              ·
                refine ⟨9566359722639040767298069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12755146296852054356397425 9566359722639040767298069)
                ·
                  refine ⟨448423111998705035967097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9566359722639040767298069 448423111998705035967097)
                  ·
                    rfl

theorem cell22_3929854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_3929854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929854 prefixEnd_3929854 := by exact prefixLift 3929854
  have htrace : WordTrace (prefixWord ++ tailWord_3929854) baseStart_3929854 baseEnd_3929854 := by
    simpa [prefixWord, tailWord_3929854, baseEnd_3929854] using wordTrace_append hprefix tailTrace_3929854
  have hstable : (prefixWord ++ tailWord_3929854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929854).length < 2 ^ (prefixWord ++ tailWord_3929854).sum := by decide
  have hdescent : baseEnd_3929854 < baseStart_3929854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929867 : List Nat := [1, 1, 1, 1, 5, 1, 5, 1, 2, 4]
def baseStart_3929867 : Nat := 118140960795 + 3929867 * 2 ^ 59
def prefixEnd_3929867 : Nat := 4983230072969 + 3 ^ 40 * 3929867 * 2
def baseEnd_3929867 : Nat := 1345273786161787407326251

theorem tailTrace_3929867 : CollatzResearch.WordTrace tailWord_3929867 prefixEnd_3929867 1345273786161787407326251 := by
  unfold tailWord_3929867
  simp only [CollatzResearch.WordTrace]
  refine ⟨143334024853770501694307855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95556016569180334462871903 143334024853770501694307855)
  ·
    refine ⟨215001037280655752541461783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143334024853770501694307855 215001037280655752541461783)
    ·
      refine ⟨322501555920983628812192675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215001037280655752541461783 322501555920983628812192675)
      ·
        refine ⟨483752333881475443218289013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322501555920983628812192675 483752333881475443218289013)
        ·
          refine ⟨45351781301388322801714595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 483752333881475443218289013 45351781301388322801714595)
          ·
            refine ⟨68027671952082484202571893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45351781301388322801714595 68027671952082484202571893)
            ·
              refine ⟨6377594245507732893991115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68027671952082484202571893 6377594245507732893991115)
              ·
                refine ⟨9566391368261599340986673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6377594245507732893991115 9566391368261599340986673)
                ·
                  refine ⟨7174793526196199505740005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9566391368261599340986673 7174793526196199505740005)
                  ·
                    refine ⟨1345273786161787407326251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7174793526196199505740005 1345273786161787407326251)
                    ·
                      rfl

theorem cell22_3929867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 4].length) (baseStart_3929867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929867 prefixEnd_3929867 := by exact prefixLift 3929867
  have htrace : WordTrace (prefixWord ++ tailWord_3929867) baseStart_3929867 baseEnd_3929867 := by
    simpa [prefixWord, tailWord_3929867, baseEnd_3929867] using wordTrace_append hprefix tailTrace_3929867
  have hstable : (prefixWord ++ tailWord_3929867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929867).length < 2 ^ (prefixWord ++ tailWord_3929867).sum := by decide
  have hdescent : baseEnd_3929867 < baseStart_3929867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929914 : List Nat := [3, 1, 1, 1, 5, 1, 2, 2, 3, 3]
def baseStart_3929914 : Nat := 118140960795 + 3929914 * 2 ^ 59
def prefixEnd_3929914 : Nat := 4983230072969 + 3 ^ 40 * 3929914 * 2
def baseEnd_3929914 : Nat := 1345289875222294951401107

theorem tailTrace_3929914 : CollatzResearch.WordTrace tailWord_3929914 prefixEnd_3929914 1345289875222294951401107 := by
  unfold tailWord_3929914
  simp only [CollatzResearch.WordTrace]
  refine ⟨35833934771150057180317199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95557159389733485814179197 35833934771150057180317199)
  ·
    refine ⟨53750902156725085770475799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35833934771150057180317199 53750902156725085770475799)
    ·
      refine ⟨80626353235087628655713699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53750902156725085770475799 80626353235087628655713699)
      ·
        refine ⟨120939529852631442983570549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80626353235087628655713699 120939529852631442983570549)
        ·
          refine ⟨11338080923684197779709739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120939529852631442983570549 11338080923684197779709739)
          ·
            refine ⟨17007121385526296669564609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11338080923684197779709739 17007121385526296669564609)
            ·
              refine ⟨12755341039144722502173457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17007121385526296669564609 12755341039144722502173457)
              ·
                refine ⟨9566505779358541876630093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12755341039144722502173457 9566505779358541876630093)
                ·
                  refine ⟨3587439667259453203736285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9566505779358541876630093 3587439667259453203736285)
                  ·
                    refine ⟨1345289875222294951401107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3587439667259453203736285 1345289875222294951401107)
                    ·
                      rfl

theorem cell22_3929914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_3929914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929914 prefixEnd_3929914 := by exact prefixLift 3929914
  have htrace : WordTrace (prefixWord ++ tailWord_3929914) baseStart_3929914 baseEnd_3929914 := by
    simpa [prefixWord, tailWord_3929914, baseEnd_3929914] using wordTrace_append hprefix tailTrace_3929914
  have hstable : (prefixWord ++ tailWord_3929914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929914).length < 2 ^ (prefixWord ++ tailWord_3929914).sum := by decide
  have hdescent : baseEnd_3929914 < baseStart_3929914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929948 : List Nat := [2, 2, 4, 2, 2, 2, 1, 1, 3, 3]
def baseStart_3929948 : Nat := 118140960795 + 3929948 * 2 ^ 59
def prefixEnd_3929948 : Nat := 4983230072969 + 3 ^ 40 * 3929948 * 2
def baseEnd_3929948 : Nat := 1345301514117130196051003

theorem tailTrace_3929948 : CollatzResearch.WordTrace tailWord_3929948 prefixEnd_3929948 1345301514117130196051003 := by
  unfold tailWord_3929948
  simp only [CollatzResearch.WordTrace]
  refine ⟨71668489583238526264003249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95557986110984701685337665 71668489583238526264003249)
  ·
    refine ⟨53751367187428894698002437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71668489583238526264003249 53751367187428894698002437)
    ·
      refine ⟨10078381347642917755875457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53751367187428894698002437 10078381347642917755875457)
      ·
        refine ⟨7558786010732188316906593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10078381347642917755875457 7558786010732188316906593)
        ·
          refine ⟨5669089508049141237679945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7558786010732188316906593 5669089508049141237679945)
          ·
            refine ⟨4251817131036855928259959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5669089508049141237679945 4251817131036855928259959)
            ·
              refine ⟨6377725696555283892389939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4251817131036855928259959 6377725696555283892389939)
              ·
                refine ⟨9566588544832925838584909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6377725696555283892389939 9566588544832925838584909)
                ·
                  refine ⟨3587470704312347189469341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9566588544832925838584909 3587470704312347189469341)
                  ·
                    refine ⟨1345301514117130196051003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3587470704312347189469341 1345301514117130196051003)
                    ·
                      rfl

theorem cell22_3929948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_3929948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929948 prefixEnd_3929948 := by exact prefixLift 3929948
  have htrace : WordTrace (prefixWord ++ tailWord_3929948) baseStart_3929948 baseEnd_3929948 := by
    simpa [prefixWord, tailWord_3929948, baseEnd_3929948] using wordTrace_append hprefix tailTrace_3929948
  have hstable : (prefixWord ++ tailWord_3929948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929948).length < 2 ^ (prefixWord ++ tailWord_3929948).sum := by decide
  have hdescent : baseEnd_3929948 < baseStart_3929948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929957 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 3, 4]
def baseStart_3929957 : Nat := 118140960795 + 3929957 * 2 ^ 59
def prefixEnd_3929957 : Nat := 4983230072969 + 3 ^ 40 * 3929957 * 2
def baseEnd_3929957 : Nat := 1345304595001057172575975

theorem tailTrace_3929957 : CollatzResearch.WordTrace tailWord_3929957 prefixEnd_3929957 1345304595001057172575975 := by
  unfold tailWord_3929957
  simp only [CollatzResearch.WordTrace]
  refine ⟨143337307423444447065084125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95558204948962964710056083 143337307423444447065084125)
  ·
    refine ⟨53751490283791667649406547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143337307423444447065084125 53751490283791667649406547)
    ·
      refine ⟨80627235425687501474109821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53751490283791667649406547 80627235425687501474109821)
      ·
        refine ⟨30235213284632813052791183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80627235425687501474109821 30235213284632813052791183)
        ·
          refine ⟨45352819926949219579186775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30235213284632813052791183 45352819926949219579186775)
          ·
            refine ⟨68029229890423829368780163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45352819926949219579186775 68029229890423829368780163)
            ·
              refine ⟨102043844835635744053170245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68029229890423829368780163 102043844835635744053170245)
              ·
                refine ⟨19133220906681702009969421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102043844835635744053170245 19133220906681702009969421)
                ·
                  refine ⟨7174957840005638253738533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19133220906681702009969421 7174957840005638253738533)
                  ·
                    refine ⟨1345304595001057172575975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7174957840005638253738533 1345304595001057172575975)
                    ·
                      rfl

theorem cell22_3929957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_3929957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929957 prefixEnd_3929957 := by exact prefixLift 3929957
  have htrace : WordTrace (prefixWord ++ tailWord_3929957) baseStart_3929957 baseEnd_3929957 := by
    simpa [prefixWord, tailWord_3929957, baseEnd_3929957] using wordTrace_append hprefix tailTrace_3929957
  have hstable : (prefixWord ++ tailWord_3929957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929957).length < 2 ^ (prefixWord ++ tailWord_3929957).sum := by decide
  have hdescent : baseEnd_3929957 < baseStart_3929957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929987 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 3, 5]
def baseStart_3929987 : Nat := 118140960795 + 3929987 * 2 ^ 59
def prefixEnd_3929987 : Nat := 4983230072969 + 3 ^ 40 * 3929987 * 2
def baseEnd_3929987 : Nat := 1345314864614147094325883

theorem tailTrace_3929987 : CollatzResearch.WordTrace tailWord_3929987 prefixEnd_3929987 1345314864614147094325883 := by
  unfold tailWord_3929987
  simp only [CollatzResearch.WordTrace]
  refine ⟨143338401613335762188676215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95558934408890508125784143 143338401613335762188676215)
  ·
    refine ⟨215007602420003643283014323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143338401613335762188676215 215007602420003643283014323)
    ·
      refine ⟨322511403630005464924521485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215007602420003643283014323 322511403630005464924521485)
      ·
        refine ⟨120941776361252049346695557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322511403630005464924521485 120941776361252049346695557)
        ·
          refine ⟨22676583067734759252505417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120941776361252049346695557 22676583067734759252505417)
          ·
            refine ⟨17007437300801069439379063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22676583067734759252505417 17007437300801069439379063)
            ·
              refine ⟨25511155951201604159068595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17007437300801069439379063 25511155951201604159068595)
              ·
                refine ⟨38266733926802406238602893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25511155951201604159068595 38266733926802406238602893)
                ·
                  refine ⟨14350025222550902339476085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38266733926802406238602893 14350025222550902339476085)
                  ·
                    refine ⟨1345314864614147094325883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14350025222550902339476085 1345314864614147094325883)
                    ·
                      rfl

theorem cell22_3929987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 5].length) (baseStart_3929987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929987 prefixEnd_3929987 := by exact prefixLift 3929987
  have htrace : WordTrace (prefixWord ++ tailWord_3929987) baseStart_3929987 baseEnd_3929987 := by
    simpa [prefixWord, tailWord_3929987, baseEnd_3929987] using wordTrace_append hprefix tailTrace_3929987
  have hstable : (prefixWord ++ tailWord_3929987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929987).length < 2 ^ (prefixWord ++ tailWord_3929987).sum := by decide
  have hdescent : baseEnd_3929987 < baseStart_3929987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929989 : List Nat := [1, 3, 1, 1, 3, 2, 2, 5, 4]
def baseStart_3929989 : Nat := 118140960795 + 3929989 * 2 ^ 59
def prefixEnd_3929989 : Nat := 4983230072969 + 3 ^ 40 * 3929989 * 2
def baseEnd_3929989 : Nat := 448438516418339918591959

theorem tailTrace_3929989 : CollatzResearch.WordTrace tailWord_3929989 prefixEnd_3929989 448438516418339918591959 := by
  unfold tailWord_3929989
  simp only [CollatzResearch.WordTrace]
  refine ⟨143338474559328516530249021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95558983039552344353499347 143338474559328516530249021)
  ·
    refine ⟨53751927959748193698843383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143338474559328516530249021 53751927959748193698843383)
    ·
      refine ⟨80627891939622290548265075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53751927959748193698843383 80627891939622290548265075)
      ·
        refine ⟨120941837909433435822397613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80627891939622290548265075 120941837909433435822397613)
        ·
          refine ⟨45353189216037538433399105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120941837909433435822397613 45353189216037538433399105)
          ·
            refine ⟨34014891912028153825049329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45353189216037538433399105 34014891912028153825049329)
            ·
              refine ⟨25511168934021115368786997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34014891912028153825049329 25511168934021115368786997)
              ·
                refine ⟨2391672087564479565823781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25511168934021115368786997 2391672087564479565823781)
                ·
                  refine ⟨448438516418339918591959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2391672087564479565823781 448438516418339918591959)
                  ·
                    rfl

theorem cell22_3929989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_3929989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3929989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3929989 prefixEnd_3929989 := by exact prefixLift 3929989
  have htrace : WordTrace (prefixWord ++ tailWord_3929989) baseStart_3929989 baseEnd_3929989 := by
    simpa [prefixWord, tailWord_3929989, baseEnd_3929989] using wordTrace_append hprefix tailTrace_3929989
  have hstable : (prefixWord ++ tailWord_3929989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929989).length < 2 ^ (prefixWord ++ tailWord_3929989).sum := by decide
  have hdescent : baseEnd_3929989 < baseStart_3929989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930092 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 2, 8]
def baseStart_3930092 : Nat := 118140960795 + 3930092 * 2 ^ 59
def prefixEnd_3930092 : Nat := 4983230072969 + 3 ^ 40 * 3930092 * 2
def baseEnd_3930092 : Nat := 1345350808259961820450561

theorem tailTrace_3930092 : CollatzResearch.WordTrace tailWord_3930092 prefixEnd_3930092 1345350808259961820450561 := by
  unfold tailWord_3930092
  simp only [CollatzResearch.WordTrace]
  refine ⟨71671115638977682560624265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95561487518636910080832353 71671115638977682560624265)
  ·
    refine ⟨53753336729233261920468199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71671115638977682560624265 53753336729233261920468199)
    ·
      refine ⟨80630005093849892880702299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53753336729233261920468199 80630005093849892880702299)
      ·
        refine ⟨120945007640774839321053449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80630005093849892880702299 120945007640774839321053449)
        ·
          refine ⟨90708755730581129490790087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120945007640774839321053449 90708755730581129490790087)
          ·
            refine ⟨136063133595871694236185131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90708755730581129490790087 136063133595871694236185131)
            ·
              refine ⟨204094700393807541354277697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136063133595871694236185131 204094700393807541354277697)
              ·
                refine ⟨153071025295355656015708273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204094700393807541354277697 153071025295355656015708273)
                ·
                  refine ⟨114803268971516742011781205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153071025295355656015708273 114803268971516742011781205)
                  ·
                    refine ⟨1345350808259961820450561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114803268971516742011781205 1345350808259961820450561)
                    ·
                      rfl

theorem cell22_3930092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_3930092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930092 prefixEnd_3930092 := by exact prefixLift 3930092
  have htrace : WordTrace (prefixWord ++ tailWord_3930092) baseStart_3930092 baseEnd_3930092 := by
    simpa [prefixWord, tailWord_3930092, baseEnd_3930092] using wordTrace_append hprefix tailTrace_3930092
  have hstable : (prefixWord ++ tailWord_3930092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930092).length < 2 ^ (prefixWord ++ tailWord_3930092).sum := by decide
  have hdescent : baseEnd_3930092 < baseStart_3930092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930107 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 8]
def baseStart_3930107 : Nat := 118140960795 + 3930107 * 2 ^ 59
def prefixEnd_3930107 : Nat := 4983230072969 + 3 ^ 40 * 3930107 * 2
def baseEnd_3930107 : Nat := 448451981022168927108505

theorem tailTrace_3930107 : CollatzResearch.WordTrace tailWord_3930107 prefixEnd_3930107 448451981022168927108505 := by
  unfold tailWord_3930107
  simp only [CollatzResearch.WordTrace]
  refine ⟨143342778372901022683044575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95561852248600681788696383 143342778372901022683044575)
  ·
    refine ⟨215014167559351534024566863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143342778372901022683044575 215014167559351534024566863)
    ·
      refine ⟨322521251339027301036850295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215014167559351534024566863 322521251339027301036850295)
      ·
        refine ⟨483781877008540951555275443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322521251339027301036850295 483781877008540951555275443)
        ·
          refine ⟨725672815512811427332913165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483781877008540951555275443 725672815512811427332913165)
          ·
            refine ⟨272127305817304285249842437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 725672815512811427332913165 272127305817304285249842437)
            ·
              refine ⟨51023869840744553484345457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272127305817304285249842437 51023869840744553484345457)
              ·
                refine ⟨38267902380558415113259093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51023869840744553484345457 38267902380558415113259093)
                ·
                  refine ⟨448451981022168927108505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38267902380558415113259093 448451981022168927108505)
                  ·
                    rfl

theorem cell22_3930107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 8].length) (baseStart_3930107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930107 prefixEnd_3930107 := by exact prefixLift 3930107
  have htrace : WordTrace (prefixWord ++ tailWord_3930107) baseStart_3930107 baseEnd_3930107 := by
    simpa [prefixWord, tailWord_3930107, baseEnd_3930107] using wordTrace_append hprefix tailTrace_3930107
  have hstable : (prefixWord ++ tailWord_3930107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930107).length < 2 ^ (prefixWord ++ tailWord_3930107).sum := by decide
  have hdescent : baseEnd_3930107 < baseStart_3930107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930139 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 6, 3]
def baseStart_3930139 : Nat := 118140960795 + 3930139 * 2 ^ 59
def prefixEnd_3930139 : Nat := 4983230072969 + 3 ^ 40 * 3930139 * 2
def baseEnd_3930139 : Nat := 1345366897320469364525417

theorem tailTrace_3930139 : CollatzResearch.WordTrace tailWord_3930139 prefixEnd_3930139 1345366897320469364525417 := by
  unfold tailWord_3930139
  simp only [CollatzResearch.WordTrace]
  refine ⟨143343945508785092148209471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95562630339190061432139647 143343945508785092148209471)
  ·
    refine ⟨215015918263177638222314207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143343945508785092148209471 215015918263177638222314207)
    ·
      refine ⟨322523877394766457333471311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215015918263177638222314207 322523877394766457333471311)
      ·
        refine ⟨483785816092149686000206967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322523877394766457333471311 483785816092149686000206967)
        ·
          refine ⟨725678724138224529000310451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483785816092149686000206967 725678724138224529000310451)
          ·
            refine ⟨1088518086207336793500465677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725678724138224529000310451 1088518086207336793500465677)
            ·
              refine ⟨408194282327751297562674629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1088518086207336793500465677 408194282327751297562674629)
              ·
                refine ⟨76536427936453368293001493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408194282327751297562674629 76536427936453368293001493)
                ·
                  refine ⟨3587645059521251638734445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76536427936453368293001493 3587645059521251638734445)
                  ·
                    refine ⟨1345366897320469364525417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3587645059521251638734445 1345366897320469364525417)
                    ·
                      rfl

theorem cell22_3930139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 3].length) (baseStart_3930139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930139 prefixEnd_3930139 := by exact prefixLift 3930139
  have htrace : WordTrace (prefixWord ++ tailWord_3930139) baseStart_3930139 baseEnd_3930139 := by
    simpa [prefixWord, tailWord_3930139, baseEnd_3930139] using wordTrace_append hprefix tailTrace_3930139
  have hstable : (prefixWord ++ tailWord_3930139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930139).length < 2 ^ (prefixWord ++ tailWord_3930139).sum := by decide
  have hdescent : baseEnd_3930139 < baseStart_3930139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930169 : List Nat := [1, 2, 1, 5, 3, 10]
def baseStart_3930169 : Nat := 118140960795 + 3930169 * 2 ^ 59
def prefixEnd_3930169 : Nat := 4983230072969 + 3 ^ 40 * 3930169 * 2
def baseEnd_3930169 : Nat := 16609594653500731929325

theorem tailTrace_3930169 : CollatzResearch.WordTrace tailWord_3930169 prefixEnd_3930169 16609594653500731929325 := by
  unfold tailWord_3930169
  simp only [CollatzResearch.WordTrace]
  refine ⟨143345039698676407271801561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95563359799117604847867707 143345039698676407271801561)
  ·
    refine ⟨107508779774007305453851171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143345039698676407271801561 107508779774007305453851171)
    ·
      refine ⟨161263169661010958180776757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107508779774007305453851171 161263169661010958180776757)
      ·
        refine ⟨15118422155719777329447821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161263169661010958180776757 15118422155719777329447821)
        ·
          refine ⟨5669408308394916498542933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15118422155719777329447821 5669408308394916498542933)
          ·
            refine ⟨16609594653500731929325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5669408308394916498542933 16609594653500731929325)
            ·
              rfl

theorem cell22_3930169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 10].length) (baseStart_3930169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930169 prefixEnd_3930169 := by exact prefixLift 3930169
  have htrace : WordTrace (prefixWord ++ tailWord_3930169) baseStart_3930169 baseEnd_3930169 := by
    simpa [prefixWord, tailWord_3930169, baseEnd_3930169] using wordTrace_append hprefix tailTrace_3930169
  have hstable : (prefixWord ++ tailWord_3930169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930169).length < 2 ^ (prefixWord ++ tailWord_3930169).sum := by decide
  have hdescent : baseEnd_3930169 < baseStart_3930169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930173 : List Nat := [1, 4, 1, 3, 1, 1, 4, 2, 2, 3]
def baseStart_3930173 : Nat := 118140960795 + 3930173 * 2 ^ 59
def prefixEnd_3930173 : Nat := 4983230072969 + 3 ^ 40 * 3930173 * 2
def baseEnd_3930173 : Nat := 1345378536215304609175313

theorem tailTrace_3930173 : CollatzResearch.WordTrace tailWord_3930173 prefixEnd_3930173 1345378536215304609175313 := by
  unfold tailWord_3930173
  simp only [CollatzResearch.WordTrace]
  refine ⟨143345185590661915954947173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95563457060441277303298115 143345185590661915954947173)
  ·
    refine ⟨26877222298249109241552595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143345185590661915954947173 26877222298249109241552595)
    ·
      refine ⟨40315833447373663862328893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26877222298249109241552595 40315833447373663862328893)
      ·
        refine ⟨15118437542765123948373335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40315833447373663862328893 15118437542765123948373335)
        ·
          refine ⟨22677656314147685922560003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15118437542765123948373335 22677656314147685922560003)
          ·
            refine ⟨34016484471221528883840005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22677656314147685922560003 34016484471221528883840005)
            ·
              refine ⟨6378090838354036665720001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34016484471221528883840005 6378090838354036665720001)
              ·
                refine ⟨4783568128765527499290001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6378090838354036665720001 4783568128765527499290001)
                ·
                  refine ⟨3587676096574145624467501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4783568128765527499290001 3587676096574145624467501)
                  ·
                    refine ⟨1345378536215304609175313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3587676096574145624467501 1345378536215304609175313)
                    ·
                      rfl

theorem cell22_3930173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_3930173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930173 prefixEnd_3930173 := by exact prefixLift 3930173
  have htrace : WordTrace (prefixWord ++ tailWord_3930173) baseStart_3930173 baseEnd_3930173 := by
    simpa [prefixWord, tailWord_3930173, baseEnd_3930173] using wordTrace_append hprefix tailTrace_3930173
  have hstable : (prefixWord ++ tailWord_3930173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930173).length < 2 ^ (prefixWord ++ tailWord_3930173).sum := by decide
  have hdescent : baseEnd_3930173 < baseStart_3930173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930201 : List Nat := [1, 2, 1, 2, 2, 1, 5, 2, 3, 3]
def baseStart_3930201 : Nat := 118140960795 + 3930201 * 2 ^ 59
def prefixEnd_3930201 : Nat := 4983230072969 + 3 ^ 40 * 3930201 * 2
def baseEnd_3930201 : Nat := 1345388121187521869475227

theorem tailTrace_3930201 : CollatzResearch.WordTrace tailWord_3930201 prefixEnd_3930201 1345388121187521869475227 := by
  unfold tailWord_3930201
  simp only [CollatzResearch.WordTrace]
  refine ⟨143346206834560476736966457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95564137889706984491310971 143346206834560476736966457)
  ·
    refine ⟨107509655125920357552724843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143346206834560476736966457 107509655125920357552724843)
    ·
      refine ⟨161264482688880536329087265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107509655125920357552724843 161264482688880536329087265)
      ·
        refine ⟨120948362016660402246815449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161264482688880536329087265 120948362016660402246815449)
        ·
          refine ⟨90711271512495301685111587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120948362016660402246815449 90711271512495301685111587)
          ·
            refine ⟨136066907268742952527667381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90711271512495301685111587 136066907268742952527667381)
            ·
              refine ⟨12756272556444651799468817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136066907268742952527667381 12756272556444651799468817)
              ·
                refine ⟨9567204417333488849601613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12756272556444651799468817 9567204417333488849601613)
                ·
                  refine ⟨3587701656500058318600605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9567204417333488849601613 3587701656500058318600605)
                  ·
                    refine ⟨1345388121187521869475227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3587701656500058318600605 1345388121187521869475227)
                    ·
                      rfl

theorem cell22_3930201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 3].length) (baseStart_3930201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930201 prefixEnd_3930201 := by exact prefixLift 3930201
  have htrace : WordTrace (prefixWord ++ tailWord_3930201) baseStart_3930201 baseEnd_3930201 := by
    simpa [prefixWord, tailWord_3930201, baseEnd_3930201] using wordTrace_append hprefix tailTrace_3930201
  have hstable : (prefixWord ++ tailWord_3930201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930201).length < 2 ^ (prefixWord ++ tailWord_3930201).sum := by decide
  have hdescent : baseEnd_3930201 < baseStart_3930201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930205 : List Nat := [1, 4, 4, 1, 1, 3, 1, 1, 2, 4]
def baseStart_3930205 : Nat := 118140960795 + 3930205 * 2 ^ 59
def prefixEnd_3930205 : Nat := 4983230072969 + 3 ^ 40 * 3930205 * 2
def baseEnd_3930205 : Nat := 1345389490469267192375215

theorem tailTrace_3930205 : CollatzResearch.WordTrace tailWord_3930205 prefixEnd_3930205 1345389490469267192375215 := by
  unfold tailWord_3930205
  simp only [CollatzResearch.WordTrace]
  refine ⟨143346352726545985420112069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95564235151030656946741379 143346352726545985420112069)
  ·
    refine ⟨26877441136227372266271013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143346352726545985420112069 26877441136227372266271013)
    ·
      refine ⟨5039520213042632299925815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26877441136227372266271013 5039520213042632299925815)
      ·
        refine ⟨7559280319563948449888723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5039520213042632299925815 7559280319563948449888723)
        ·
          refine ⟨11338920479345922674833085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7559280319563948449888723 11338920479345922674833085)
          ·
            refine ⟨4252095179754721003062407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11338920479345922674833085 4252095179754721003062407)
            ·
              refine ⟨6378142769632081504593611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4252095179754721003062407 6378142769632081504593611)
              ·
                refine ⟨9567214154448122256890417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6378142769632081504593611 9567214154448122256890417)
                ·
                  refine ⟨7175410615836091692667813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9567214154448122256890417 7175410615836091692667813)
                  ·
                    refine ⟨1345389490469267192375215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7175410615836091692667813 1345389490469267192375215)
                    ·
                      rfl

theorem cell22_3930205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_3930205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930205 prefixEnd_3930205 := by exact prefixLift 3930205
  have htrace : WordTrace (prefixWord ++ tailWord_3930205) baseStart_3930205 baseEnd_3930205 := by
    simpa [prefixWord, tailWord_3930205, baseEnd_3930205] using wordTrace_append hprefix tailTrace_3930205
  have hstable : (prefixWord ++ tailWord_3930205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930205).length < 2 ^ (prefixWord ++ tailWord_3930205).sum := by decide
  have hdescent : baseEnd_3930205 < baseStart_3930205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930231 : List Nat := [1, 1, 3, 1, 1, 5, 3, 2, 5]
def baseStart_3930231 : Nat := 118140960795 + 3930231 * 2 ^ 59
def prefixEnd_3930231 : Nat := 4983230072969 + 3 ^ 40 * 3930231 * 2
def baseEnd_3930231 : Nat := 448466130266870597075045

theorem tailTrace_3930231 : CollatzResearch.WordTrace tailWord_3930231 prefixEnd_3930231 448466130266870597075045 := by
  unfold tailWord_3930231
  simp only [CollatzResearch.WordTrace]
  refine ⟨143347301024451791860558547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95564867349634527907039031 143347301024451791860558547)
  ·
    refine ⟨215020951536677687790837821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143347301024451791860558547 215020951536677687790837821)
    ·
      refine ⟨80632856826254132921564183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215020951536677687790837821 80632856826254132921564183)
      ·
        refine ⟨120949285239381199382346275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80632856826254132921564183 120949285239381199382346275)
        ·
          refine ⟨181423927859071799073519413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120949285239381199382346275 181423927859071799073519413)
          ·
            refine ⟨17008493236787981163142445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181423927859071799073519413 17008493236787981163142445)
            ·
              refine ⟨6378184963795492936178417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17008493236787981163142445 6378184963795492936178417)
              ·
                refine ⟨4783638722846619702133813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6378184963795492936178417 4783638722846619702133813)
                ·
                  refine ⟨448466130266870597075045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4783638722846619702133813 448466130266870597075045)
                  ·
                    rfl

theorem cell22_3930231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 5].length) (baseStart_3930231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930231 prefixEnd_3930231 := by exact prefixLift 3930231
  have htrace : WordTrace (prefixWord ++ tailWord_3930231) baseStart_3930231 baseEnd_3930231 := by
    simpa [prefixWord, tailWord_3930231, baseEnd_3930231] using wordTrace_append hprefix tailTrace_3930231
  have hstable : (prefixWord ++ tailWord_3930231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930231).length < 2 ^ (prefixWord ++ tailWord_3930231).sum := by decide
  have hdescent : baseEnd_3930231 < baseStart_3930231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930286 : List Nat := [4, 1, 4, 2, 1, 1, 3, 2, 1, 3]
def baseStart_3930286 : Nat := 118140960795 + 3930286 * 2 ^ 59
def prefixEnd_3930286 : Nat := 4983230072969 + 3 ^ 40 * 3930286 * 2
def baseEnd_3930286 : Nat := 1345417218424609981099967

theorem tailTrace_3930286 : CollatzResearch.WordTrace tailWord_3930286 prefixEnd_3930286 1345417218424609981099967 := by
  unfold tailWord_3930286
  simp only [CollatzResearch.WordTrace]
  refine ⟨17918663379906567031726339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95566204692835024169207141 17918663379906567031726339)
  ·
    refine ⟨26877995069859850547589509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17918663379906567031726339 26877995069859850547589509)
    ·
      refine ⟨5039624075598721977673033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26877995069859850547589509 5039624075598721977673033)
      ·
        refine ⟨3779718056699041483254775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5039624075598721977673033 3779718056699041483254775)
        ·
          refine ⟨5669577085048562224882163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3779718056699041483254775 5669577085048562224882163)
          ·
            refine ⟨8504365627572843337323245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5669577085048562224882163 8504365627572843337323245)
            ·
              refine ⟨3189137110339816251496217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8504365627572843337323245 3189137110339816251496217)
              ·
                refine ⟨2391852832754862188622163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3189137110339816251496217 2391852832754862188622163)
                ·
                  refine ⟨3587779249132293282933245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2391852832754862188622163 3587779249132293282933245)
                  ·
                    refine ⟨1345417218424609981099967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3587779249132293282933245 1345417218424609981099967)
                    ·
                      rfl

theorem cell22_3930286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_3930286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930286 prefixEnd_3930286 := by exact prefixLift 3930286
  have htrace : WordTrace (prefixWord ++ tailWord_3930286) baseStart_3930286 baseEnd_3930286 := by
    simpa [prefixWord, tailWord_3930286, baseEnd_3930286] using wordTrace_append hprefix tailTrace_3930286
  have hstable : (prefixWord ++ tailWord_3930286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930286).length < 2 ^ (prefixWord ++ tailWord_3930286).sum := by decide
  have hdescent : baseEnd_3930286 < baseStart_3930286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930351 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 2, 6]
def baseStart_3930351 : Nat := 118140960795 + 3930351 * 2 ^ 59
def prefixEnd_3930351 : Nat := 4983230072969 + 3 ^ 40 * 3930351 * 2
def baseEnd_3930351 : Nat := 1345439469252971478224767

theorem tailTrace_3930351 : CollatzResearch.WordTrace tailWord_3930351 prefixEnd_3930351 1345439469252971478224767 := by
  unfold tailWord_3930351
  simp only [CollatzResearch.WordTrace]
  refine ⟨143351677784017052354926907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95567785189344701569951271 143351677784017052354926907)
  ·
    refine ⟨215027516676025578532390361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143351677784017052354926907 215027516676025578532390361)
    ·
      refine ⟨161270637507019183899292771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215027516676025578532390361 161270637507019183899292771)
      ·
        refine ⟨241905956260528775848939157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161270637507019183899292771 241905956260528775848939157)
        ·
          refine ⟨11339341699712286367919023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 241905956260528775848939157 11339341699712286367919023)
          ·
            refine ⟨17009012549568429551878535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11339341699712286367919023 17009012549568429551878535)
            ·
              refine ⟨25513518824352644327817803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17009012549568429551878535 25513518824352644327817803)
              ·
                refine ⟨38270278236528966491726705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25513518824352644327817803 38270278236528966491726705)
                ·
                  refine ⟨28702708677396724868795029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38270278236528966491726705 28702708677396724868795029)
                  ·
                    refine ⟨1345439469252971478224767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28702708677396724868795029 1345439469252971478224767)
                    ·
                      rfl

theorem cell22_3930351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_3930351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930351 prefixEnd_3930351 := by exact prefixLift 3930351
  have htrace : WordTrace (prefixWord ++ tailWord_3930351) baseStart_3930351 baseEnd_3930351 := by
    simpa [prefixWord, tailWord_3930351, baseEnd_3930351] using wordTrace_append hprefix tailTrace_3930351
  have hstable : (prefixWord ++ tailWord_3930351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930351).length < 2 ^ (prefixWord ++ tailWord_3930351).sum := by decide
  have hdescent : baseEnd_3930351 < baseStart_3930351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930370 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_3930370 : Nat := 118140960795 + 3930370 * 2 ^ 59
def prefixEnd_3930370 : Nat := 4983230072969 + 3 ^ 40 * 3930370 * 2
def baseEnd_3930370 : Nat := 1345445973341261761999709

theorem tailTrace_3930370 : CollatzResearch.WordTrace tailWord_3930370 prefixEnd_3930370 1345445973341261761999709 := by
  unfold tailWord_3930370
  simp only [CollatzResearch.WordTrace]
  refine ⟨35838092692737054649967141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95568247180632145733245709 35838092692737054649967141)
  ·
    refine ⟨6719642379888197746868839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35838092692737054649967141 6719642379888197746868839)
    ·
      refine ⟨10079463569832296620303259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6719642379888197746868839 10079463569832296620303259)
      ·
        refine ⟨15119195354748444930454889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10079463569832296620303259 15119195354748444930454889)
        ·
          refine ⟨11339396516061333697841167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15119195354748444930454889 11339396516061333697841167)
          ·
            refine ⟨17009094774092000546761751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11339396516061333697841167 17009094774092000546761751)
            ·
              refine ⟨25513642161138000820142627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17009094774092000546761751 25513642161138000820142627)
              ·
                refine ⟨38270463241707001230213941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25513642161138000820142627 38270463241707001230213941)
                ·
                  refine ⟨3587855928910031365332557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38270463241707001230213941 3587855928910031365332557)
                  ·
                    refine ⟨1345445973341261761999709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3587855928910031365332557 1345445973341261761999709)
                    ·
                      rfl

theorem cell22_3930370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_3930370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930370 prefixEnd_3930370 := by exact prefixLift 3930370
  have htrace : WordTrace (prefixWord ++ tailWord_3930370) baseStart_3930370 baseEnd_3930370 := by
    simpa [prefixWord, tailWord_3930370, baseEnd_3930370] using wordTrace_append hprefix tailTrace_3930370
  have hstable : (prefixWord ++ tailWord_3930370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930370).length < 2 ^ (prefixWord ++ tailWord_3930370).sum := by decide
  have hdescent : baseEnd_3930370 < baseStart_3930370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930400 : List Nat := [2, 1, 1, 5, 2, 3, 1, 2, 5]
def baseStart_3930400 : Nat := 118140960795 + 3930400 * 2 ^ 59
def prefixEnd_3930400 : Nat := 4983230072969 + 3 ^ 40 * 3930400 * 2
def baseEnd_3930400 : Nat := 448485414318117227916539

theorem tailTrace_3930400 : CollatzResearch.WordTrace tailWord_3930400 prefixEnd_3930400 448485414318117227916539 := by
  unfold tailWord_3930400
  simp only [CollatzResearch.WordTrace]
  refine ⟨71676732480419766861730327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95568976640559689148973769 71676732480419766861730327)
  ·
    refine ⟨107515098720629650292595491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71676732480419766861730327 107515098720629650292595491)
    ·
      refine ⟨161272648080944475438893237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107515098720629650292595491 161272648080944475438893237)
      ·
        refine ⟨15119310757588544572396241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161272648080944475438893237 15119310757588544572396241)
        ·
          refine ⟨11339483068191408429297181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15119310757588544572396241 11339483068191408429297181)
          ·
            refine ⟨4252306150571778160986443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11339483068191408429297181 4252306150571778160986443)
            ·
              refine ⟨6378459225857667241479665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4252306150571778160986443 6378459225857667241479665)
              ·
                refine ⟨4783844419393250431109749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6378459225857667241479665 4783844419393250431109749)
                ·
                  refine ⟨448485414318117227916539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4783844419393250431109749 448485414318117227916539)
                  ·
                    rfl

theorem cell22_3930400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 5].length) (baseStart_3930400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930400 prefixEnd_3930400 := by exact prefixLift 3930400
  have htrace : WordTrace (prefixWord ++ tailWord_3930400) baseStart_3930400 baseEnd_3930400 := by
    simpa [prefixWord, tailWord_3930400, baseEnd_3930400] using wordTrace_append hprefix tailTrace_3930400
  have hstable : (prefixWord ++ tailWord_3930400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930400).length < 2 ^ (prefixWord ++ tailWord_3930400).sum := by decide
  have hdescent : baseEnd_3930400 < baseStart_3930400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930430 : List Nat := [4, 2, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_3930430 : Nat := 118140960795 + 3930430 * 2 ^ 59
def prefixEnd_3930430 : Nat := 4983230072969 + 3 ^ 40 * 3930430 * 2
def baseEnd_3930430 : Nat := 1345466512567441605499525

theorem tailTrace_3930430 : CollatzResearch.WordTrace tailWord_3930430 prefixEnd_3930430 1345466512567441605499525 := by
  unfold tailWord_3930430
  simp only [CollatzResearch.WordTrace]
  refine ⟨17919319893841356105881593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95569706100487232564701829 17919319893841356105881593)
  ·
    refine ⟨13439489920381017079411195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17919319893841356105881593 13439489920381017079411195)
    ·
      refine ⟨20159234880571525619116793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13439489920381017079411195 20159234880571525619116793)
      ·
        refine ⟨15119426160428644214337595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20159234880571525619116793 15119426160428644214337595)
        ·
          refine ⟨22679139240642966321506393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15119426160428644214337595 22679139240642966321506393)
          ·
            refine ⟨17009354430482224741129795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22679139240642966321506393 17009354430482224741129795)
            ·
              refine ⟨25514031645723337111694693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17009354430482224741129795 25514031645723337111694693)
              ·
                refine ⟨4783880933573125708442755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25514031645723337111694693 4783880933573125708442755)
                ·
                  refine ⟨7175821400359688562664133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4783880933573125708442755 7175821400359688562664133)
                  ·
                    refine ⟨1345466512567441605499525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7175821400359688562664133 1345466512567441605499525)
                    ·
                      rfl

theorem cell22_3930430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_3930430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930430 prefixEnd_3930430 := by exact prefixLift 3930430
  have htrace : WordTrace (prefixWord ++ tailWord_3930430) baseStart_3930430 baseEnd_3930430 := by
    simpa [prefixWord, tailWord_3930430, baseEnd_3930430] using wordTrace_append hprefix tailTrace_3930430
  have hstable : (prefixWord ++ tailWord_3930430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930430).length < 2 ^ (prefixWord ++ tailWord_3930430).sum := by decide
  have hdescent : baseEnd_3930430 < baseStart_3930430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930533 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 2, 5]
def baseStart_3930533 : Nat := 118140960795 + 3930533 * 2 ^ 59
def prefixEnd_3930533 : Nat := 4983230072969 + 3 ^ 40 * 3930533 * 2
def baseEnd_3930533 : Nat := 1345501771572383670174209

theorem tailTrace_3930533 : CollatzResearch.WordTrace tailWord_3930533 prefixEnd_3930533 1345501771572383670174209 := by
  unfold tailWord_3930533
  simp only [CollatzResearch.WordTrace]
  refine ⟨143358315869357697438052253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95572210579571798292034835 143358315869357697438052253)
  ·
    refine ⟨53759368451009136539269595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143358315869357697438052253 53759368451009136539269595)
    ·
      refine ⟨80639052676513704808904393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53759368451009136539269595 80639052676513704808904393)
      ·
        refine ⟨60479289507385278606678295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80639052676513704808904393 60479289507385278606678295)
        ·
          refine ⟨90718934261077917910017443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60479289507385278606678295 90718934261077917910017443)
          ·
            refine ⟨136078401391616876865026165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90718934261077917910017443 136078401391616876865026165)
            ·
              refine ⟨12757350130464082206096203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136078401391616876865026165 12757350130464082206096203)
              ·
                refine ⟨19136025195696123309144305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12757350130464082206096203 19136025195696123309144305)
                ·
                  refine ⟨14352018896772092481858229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19136025195696123309144305 14352018896772092481858229)
                  ·
                    refine ⟨1345501771572383670174209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14352018896772092481858229 1345501771572383670174209)
                    ·
                      rfl

theorem cell22_3930533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_3930533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930533 prefixEnd_3930533 := by exact prefixLift 3930533
  have htrace : WordTrace (prefixWord ++ tailWord_3930533) baseStart_3930533 baseEnd_3930533 := by
    simpa [prefixWord, tailWord_3930533, baseEnd_3930533] using wordTrace_append hprefix tailTrace_3930533
  have hstable : (prefixWord ++ tailWord_3930533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930533).length < 2 ^ (prefixWord ++ tailWord_3930533).sum := by decide
  have hdescent : baseEnd_3930533 < baseStart_3930533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930535 : List Nat := [1, 1, 6, 1, 1, 2, 2, 3, 5]
def baseStart_3930535 : Nat := 118140960795 + 3930535 * 2 ^ 59
def prefixEnd_3930535 : Nat := 4983230072969 + 3 ^ 40 * 3930535 * 2
def baseEnd_3930535 : Nat := 448500818737752110541401

theorem tailTrace_3930535 : CollatzResearch.WordTrace tailWord_3930535 prefixEnd_3930535 448500818737752110541401 := by
  unfold tailWord_3930535
  simp only [CollatzResearch.WordTrace]
  refine ⟨143358388815350451779625059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95572259210233634519750039 143358388815350451779625059)
  ·
    refine ⟨215037583223025677669437589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143358388815350451779625059 215037583223025677669437589)
    ·
      refine ⟨10079886713579328640754887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 215037583223025677669437589 10079886713579328640754887)
      ·
        refine ⟨15119830070368992961132331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10079886713579328640754887 15119830070368992961132331)
        ·
          refine ⟨22679745105553489441698497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15119830070368992961132331 22679745105553489441698497)
          ·
            refine ⟨17009808829165117081273873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22679745105553489441698497 17009808829165117081273873)
            ·
              refine ⟨12757356621873837810955405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17009808829165117081273873 12757356621873837810955405)
              ·
                refine ⟨4784008733202689179108277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12757356621873837810955405 4784008733202689179108277)
                ·
                  refine ⟨448500818737752110541401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4784008733202689179108277 448500818737752110541401)
                  ·
                    rfl

theorem cell22_3930535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 5].length) (baseStart_3930535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930535 prefixEnd_3930535 := by exact prefixLift 3930535
  have htrace : WordTrace (prefixWord ++ tailWord_3930535) baseStart_3930535 baseEnd_3930535 := by
    simpa [prefixWord, tailWord_3930535, baseEnd_3930535] using wordTrace_append hprefix tailTrace_3930535
  have hstable : (prefixWord ++ tailWord_3930535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930535).length < 2 ^ (prefixWord ++ tailWord_3930535).sum := by decide
  have hdescent : baseEnd_3930535 < baseStart_3930535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930580 : List Nat := [2, 4, 1, 2, 2, 1, 1, 3, 6]
def baseStart_3930580 : Nat := 118140960795 + 3930580 * 2 ^ 59
def prefixEnd_3930580 : Nat := 4983230072969 + 3 ^ 40 * 3930580 * 2
def baseEnd_3930580 : Nat := 448505953544297071416355

theorem tailTrace_3930580 : CollatzResearch.WordTrace tailWord_3930580 prefixEnd_3930580 448505953544297071416355 := by
  unfold tailWord_3930580
  simp only [CollatzResearch.WordTrace]
  refine ⟨71680015050093712232506597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95573353400124949643342129 71680015050093712232506597)
  ·
    refine ⟨13440002821892571043594987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71680015050093712232506597 13440002821892571043594987)
    ·
      refine ⟨20160004232838856565392481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13440002821892571043594987 20160004232838856565392481)
      ·
        refine ⟨15120003174629142424044361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20160004232838856565392481 15120003174629142424044361)
        ·
          refine ⟨11340002380971856818033271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15120003174629142424044361 11340002380971856818033271)
          ·
            refine ⟨17010003571457785227049907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11340002380971856818033271 17010003571457785227049907)
            ·
              refine ⟨25515005357186677840574861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17010003571457785227049907 25515005357186677840574861)
              ·
                refine ⟨9568127008945004190215573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25515005357186677840574861 9568127008945004190215573)
                ·
                  refine ⟨448505953544297071416355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9568127008945004190215573 448505953544297071416355)
                  ·
                    rfl

theorem cell22_3930580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_3930580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930580 prefixEnd_3930580 := by exact prefixLift 3930580
  have htrace : WordTrace (prefixWord ++ tailWord_3930580) baseStart_3930580 baseEnd_3930580 := by
    simpa [prefixWord, tailWord_3930580, baseEnd_3930580] using wordTrace_append hprefix tailTrace_3930580
  have hstable : (prefixWord ++ tailWord_3930580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930580).length < 2 ^ (prefixWord ++ tailWord_3930580).sum := by decide
  have hdescent : baseEnd_3930580 < baseStart_3930580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930593 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 3, 6]
def baseStart_3930593 : Nat := 118140960795 + 3930593 * 2 ^ 59
def prefixEnd_3930593 : Nat := 4983230072969 + 3 ^ 40 * 3930593 * 2
def baseEnd_3930593 : Nat := 1345522310798563513674025

theorem tailTrace_3930593 : CollatzResearch.WordTrace tailWord_3930593 prefixEnd_3930593 1345522310798563513674025 := by
  unfold tailWord_3930593
  simp only [CollatzResearch.WordTrace]
  refine ⟨143360504249140327685236433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95573669499426885123490955 143360504249140327685236433)
  ·
    refine ⟨107520378186855245763927325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143360504249140327685236433 107520378186855245763927325)
    ·
      refine ⟨40320141820070717161472747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107520378186855245763927325 40320141820070717161472747)
      ·
        refine ⟨60480212730106075742209121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40320141820070717161472747 60480212730106075742209121)
        ·
          refine ⟨45360159547579556806656841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60480212730106075742209121 45360159547579556806656841)
          ·
            refine ⟨34020119660684667604992631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45360159547579556806656841 34020119660684667604992631)
            ·
              refine ⟨51030179491027001407488947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34020119660684667604992631 51030179491027001407488947)
              ·
                refine ⟨76545269236540502111233421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51030179491027001407488947 76545269236540502111233421)
                ·
                  refine ⟨28704475963702688291712533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76545269236540502111233421 28704475963702688291712533)
                  ·
                    refine ⟨1345522310798563513674025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28704475963702688291712533 1345522310798563513674025)
                    ·
                      rfl

theorem cell22_3930593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_3930593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930593 prefixEnd_3930593 := by exact prefixLift 3930593
  have htrace : WordTrace (prefixWord ++ tailWord_3930593) baseStart_3930593 baseEnd_3930593 := by
    simpa [prefixWord, tailWord_3930593, baseEnd_3930593] using wordTrace_append hprefix tailTrace_3930593
  have hstable : (prefixWord ++ tailWord_3930593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930593).length < 2 ^ (prefixWord ++ tailWord_3930593).sum := by decide
  have hdescent : baseEnd_3930593 < baseStart_3930593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930608 : List Nat := [2, 1, 1, 1, 3, 3, 3, 8]
def baseStart_3930608 : Nat := 118140960795 + 3930608 * 2 ^ 59
def prefixEnd_3930608 : Nat := 4983230072969 + 3 ^ 40 * 3930608 * 2
def baseEnd_3930608 : Nat := 149503049511678719394331

theorem tailTrace_3930608 : CollatzResearch.WordTrace tailWord_3930608 prefixEnd_3930608 149503049511678719394331 := by
  unfold tailWord_3930608
  simp only [CollatzResearch.WordTrace]
  refine ⟨71680525672042992623516239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95574034229390656831354985 71680525672042992623516239)
  ·
    refine ⟨107520788508064488935274359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71680525672042992623516239 107520788508064488935274359)
    ·
      refine ⟨161281182762096733402911539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107520788508064488935274359 161281182762096733402911539)
      ·
        refine ⟨241921774143145100104367309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161281182762096733402911539 241921774143145100104367309)
        ·
          refine ⟨90720665303679412539137741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241921774143145100104367309 90720665303679412539137741)
          ·
            refine ⟨34020249488879779702176653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90720665303679412539137741 34020249488879779702176653)
            ·
              refine ⟨12757593558329917388316245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34020249488879779702176653 12757593558329917388316245)
              ·
                refine ⟨149503049511678719394331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12757593558329917388316245 149503049511678719394331)
                ·
                  rfl

theorem cell22_3930608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 8].length) (baseStart_3930608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930608 prefixEnd_3930608 := by exact prefixLift 3930608
  have htrace : WordTrace (prefixWord ++ tailWord_3930608) baseStart_3930608 baseEnd_3930608 := by
    simpa [prefixWord, tailWord_3930608, baseEnd_3930608] using wordTrace_append hprefix tailTrace_3930608
  have hstable : (prefixWord ++ tailWord_3930608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930608).length < 2 ^ (prefixWord ++ tailWord_3930608).sum := by decide
  have hdescent : baseEnd_3930608 < baseStart_3930608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930625 : List Nat := [1, 2, 4, 1, 3, 3, 8]
def baseStart_3930625 : Nat := 118140960795 + 3930625 * 2 ^ 59
def prefixEnd_3930625 : Nat := 4983230072969 + 3 ^ 40 * 3930625 * 2
def baseEnd_3930625 : Nat := 49834565372315781365701

theorem tailTrace_3930625 : CollatzResearch.WordTrace tailWord_3930625 prefixEnd_3930625 49834565372315781365701 := by
  unfold tailWord_3930625
  simp only [CollatzResearch.WordTrace]
  refine ⟨143361671385024397150401329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95574447590016264766934219 143361671385024397150401329)
  ·
    refine ⟨107521253538768297862800997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143361671385024397150401329 107521253538768297862800997)
    ·
      refine ⟨20160235038519055849275187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107521253538768297862800997 20160235038519055849275187)
      ·
        refine ⟨30240352557778583773912781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20160235038519055849275187 30240352557778583773912781)
        ·
          refine ⟨11340132209166968915217293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30240352557778583773912781 11340132209166968915217293)
          ·
            refine ⟨4252549578437613343206485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11340132209166968915217293 4252549578437613343206485)
            ·
              refine ⟨49834565372315781365701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4252549578437613343206485 49834565372315781365701)
              ·
                rfl

theorem cell22_3930625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 8].length) (baseStart_3930625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930625 prefixEnd_3930625 := by exact prefixLift 3930625
  have htrace : WordTrace (prefixWord ++ tailWord_3930625) baseStart_3930625 baseEnd_3930625 := by
    simpa [prefixWord, tailWord_3930625, baseEnd_3930625] using wordTrace_append hprefix tailTrace_3930625
  have hstable : (prefixWord ++ tailWord_3930625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930625).length < 2 ^ (prefixWord ++ tailWord_3930625).sum := by decide
  have hdescent : baseEnd_3930625 < baseStart_3930625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930683 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 4, 8]
def baseStart_3930683 : Nat := 118140960795 + 3930683 * 2 ^ 59
def prefixEnd_3930683 : Nat := 4983230072969 + 3 ^ 40 * 3930683 * 2
def baseEnd_3930683 : Nat := 1345553119637833278923749

theorem tailTrace_3930683 : CollatzResearch.WordTrace tailWord_3930683 prefixEnd_3930683 1345553119637833278923749 := by
  unfold tailWord_3930683
  simp only [CollatzResearch.WordTrace]
  refine ⟨143363786818814273056012703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95575857879209515370675135 143363786818814273056012703)
  ·
    refine ⟨215045680228221409584019055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143363786818814273056012703 215045680228221409584019055)
    ·
      refine ⟨322568520342332114376028583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215045680228221409584019055 322568520342332114376028583)
      ·
        refine ⟨483852780513498171564042875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322568520342332114376028583 483852780513498171564042875)
        ·
          refine ⟨725779170770247257346064313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483852780513498171564042875 725779170770247257346064313)
          ·
            refine ⟨544334378077685443009548235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 725779170770247257346064313 544334378077685443009548235)
            ·
              refine ⟨816501567116528164514322353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544334378077685443009548235 816501567116528164514322353)
              ·
                refine ⟨612376175337396123385741765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 816501567116528164514322353 612376175337396123385741765)
                ·
                  refine ⟨114820532875761773134826581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 612376175337396123385741765 114820532875761773134826581)
                  ·
                    refine ⟨1345553119637833278923749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114820532875761773134826581 1345553119637833278923749)
                    ·
                      rfl

theorem cell22_3930683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 8].length) (baseStart_3930683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930683 prefixEnd_3930683 := by exact prefixLift 3930683
  have htrace : WordTrace (prefixWord ++ tailWord_3930683) baseStart_3930683 baseEnd_3930683 := by
    simpa [prefixWord, tailWord_3930683, baseEnd_3930683] using wordTrace_append hprefix tailTrace_3930683
  have hstable : (prefixWord ++ tailWord_3930683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930683).length < 2 ^ (prefixWord ++ tailWord_3930683).sum := by decide
  have hdescent : baseEnd_3930683 < baseStart_3930683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930700 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 5, 4]
def baseStart_3930700 : Nat := 118140960795 + 3930700 * 2 ^ 59
def prefixEnd_3930700 : Nat := 4983230072969 + 3 ^ 40 * 3930700 * 2
def baseEnd_3930700 : Nat := 1345558939085250901248697

theorem tailTrace_3930700 : CollatzResearch.WordTrace tailWord_3930700 prefixEnd_3930700 1345558939085250901248697 := by
  unfold tailWord_3930700
  simp only [CollatzResearch.WordTrace]
  refine ⟨71682203429876342479690777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95576271239835123306254369 71682203429876342479690777)
  ·
    refine ⟨53761652572407256859768083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71682203429876342479690777 53761652572407256859768083)
    ·
      refine ⟨80642478858610885289652125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53761652572407256859768083 80642478858610885289652125)
      ·
        refine ⟨30240929571979081983619547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80642478858610885289652125 30240929571979081983619547)
        ·
          refine ⟨45361394357968622975429321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30240929571979081983619547 45361394357968622975429321)
          ·
            refine ⟨34021045768476467231571991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45361394357968622975429321 34021045768476467231571991)
            ·
              refine ⟨51031568652714700847357987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34021045768476467231571991 51031568652714700847357987)
              ·
                refine ⟨76547352979072051271036981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51031568652714700847357987 76547352979072051271036981)
                ·
                  refine ⟨7176314341788004806659717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76547352979072051271036981 7176314341788004806659717)
                  ·
                    refine ⟨1345558939085250901248697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7176314341788004806659717 1345558939085250901248697)
                    ·
                      rfl

theorem cell22_3930700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_3930700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930700 prefixEnd_3930700 := by exact prefixLift 3930700
  have htrace : WordTrace (prefixWord ++ tailWord_3930700) baseStart_3930700 baseEnd_3930700 := by
    simpa [prefixWord, tailWord_3930700, baseEnd_3930700] using wordTrace_append hprefix tailTrace_3930700
  have hstable : (prefixWord ++ tailWord_3930700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930700).length < 2 ^ (prefixWord ++ tailWord_3930700).sum := by decide
  have hdescent : baseEnd_3930700 < baseStart_3930700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930732 : List Nat := [2, 2, 1, 1, 3, 1, 3, 5, 4]
def baseStart_3930732 : Nat := 118140960795 + 3930732 * 2 ^ 59
def prefixEnd_3930732 : Nat := 4983230072969 + 3 ^ 40 * 3930732 * 2
def baseEnd_3930732 : Nat := 448523297779737828149533

theorem tailTrace_3930732 : CollatzResearch.WordTrace tailWord_3930732 prefixEnd_3930732 448523297779737828149533 := by
  unfold tailWord_3930732
  simp only [CollatzResearch.WordTrace]
  refine ⟨71682786997818377212273225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95577049330424502949697633 71682786997818377212273225)
  ·
    refine ⟨53762090248363782909204919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71682786997818377212273225 53762090248363782909204919)
    ·
      refine ⟨80643135372545674363807379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53762090248363782909204919 80643135372545674363807379)
      ·
        refine ⟨120964703058818511545711069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80643135372545674363807379 120964703058818511545711069)
        ·
          refine ⟨45361763647056941829641651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120964703058818511545711069 45361763647056941829641651)
          ·
            refine ⟨68042645470585412744462477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45361763647056941829641651 68042645470585412744462477)
            ·
              refine ⟨25515992051469529779173429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68042645470585412744462477 25515992051469529779173429)
              ·
                refine ⟨2392124254825268416797509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25515992051469529779173429 2392124254825268416797509)
                ·
                  refine ⟨448523297779737828149533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2392124254825268416797509 448523297779737828149533)
                  ·
                    rfl

theorem cell22_3930732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_3930732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930732 prefixEnd_3930732 := by exact prefixLift 3930732
  have htrace : WordTrace (prefixWord ++ tailWord_3930732) baseStart_3930732 baseEnd_3930732 := by
    simpa [prefixWord, tailWord_3930732, baseEnd_3930732] using wordTrace_append hprefix tailTrace_3930732
  have hstable : (prefixWord ++ tailWord_3930732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930732).length < 2 ^ (prefixWord ++ tailWord_3930732).sum := by decide
  have hdescent : baseEnd_3930732 < baseStart_3930732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930734 : List Nat := [4, 1, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_3930734 : Nat := 118140960795 + 3930734 * 2 ^ 59
def prefixEnd_3930734 : Nat := 4983230072969 + 3 ^ 40 * 3930734 * 2
def baseEnd_3930734 : Nat := 1345570577980086145898593

theorem tailTrace_3930734 : CollatzResearch.WordTrace tailWord_3930734 prefixEnd_3930734 1345570577980086145898593 := by
  unfold tailWord_3930734
  simp only [CollatzResearch.WordTrace]
  refine ⟨17920705867703688595764907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95577097961086339177412837 17920705867703688595764907)
  ·
    refine ⟨26881058801555532893647361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17920705867703688595764907 26881058801555532893647361)
    ·
      refine ⟨20160794101166649670235521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26881058801555532893647361 20160794101166649670235521)
      ·
        refine ⟨15120595575874987252676641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20160794101166649670235521 15120595575874987252676641)
        ·
          refine ⟨11340446681906240439507481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15120595575874987252676641 11340446681906240439507481)
          ·
            refine ⟨8505335011429680329630611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11340446681906240439507481 8505335011429680329630611)
            ·
              refine ⟨12758002517144520494445917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8505335011429680329630611 12758002517144520494445917)
              ·
                refine ⟨4784250943929195185417219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12758002517144520494445917 4784250943929195185417219)
                ·
                  refine ⟨7176376415893792778125829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4784250943929195185417219 7176376415893792778125829)
                  ·
                    refine ⟨1345570577980086145898593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7176376415893792778125829 1345570577980086145898593)
                    ·
                      rfl

theorem cell22_3930734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_3930734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930734 prefixEnd_3930734 := by exact prefixLift 3930734
  have htrace : WordTrace (prefixWord ++ tailWord_3930734) baseStart_3930734 baseEnd_3930734 := by
    simpa [prefixWord, tailWord_3930734, baseEnd_3930734] using wordTrace_append hprefix tailTrace_3930734
  have hstable : (prefixWord ++ tailWord_3930734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930734).length < 2 ^ (prefixWord ++ tailWord_3930734).sum := by decide
  have hdescent : baseEnd_3930734 < baseStart_3930734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930747 : List Nat := [1, 1, 1, 1, 1, 4, 2, 6, 2, 3]
def baseStart_3930747 : Nat := 118140960795 + 3930747 * 2 ^ 59
def prefixEnd_3930747 : Nat := 4983230072969 + 3 ^ 40 * 3930747 * 2
def baseEnd_3930747 : Nat := 1345575028145758445323553

theorem tailTrace_3930747 : CollatzResearch.WordTrace tailWord_3930747 prefixEnd_3930747 1345575028145758445323553 := by
  unfold tailWord_3930747
  simp only [CollatzResearch.WordTrace]
  refine ⟨143366121090582411986342495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95577414060388274657561663 143366121090582411986342495)
  ·
    refine ⟨215049181635873617979513743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143366121090582411986342495 215049181635873617979513743)
    ·
      refine ⟨322573772453810426969270615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215049181635873617979513743 322573772453810426969270615)
      ·
        refine ⟨483860658680715640453905923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322573772453810426969270615 483860658680715640453905923)
        ·
          refine ⟨725790988021073460680858885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483860658680715640453905923 725790988021073460680858885)
          ·
            refine ⟨136085810253951273877661041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 725790988021073460680858885 136085810253951273877661041)
            ·
              refine ⟨102064357690463455408245781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136085810253951273877661041 102064357690463455408245781)
              ·
                refine ⟨4784266766740474472261521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102064357690463455408245781 4784266766740474472261521)
                ·
                  refine ⟨3588200075055355854196141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4784266766740474472261521 3588200075055355854196141)
                  ·
                    refine ⟨1345575028145758445323553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3588200075055355854196141 1345575028145758445323553)
                    ·
                      rfl

theorem cell22_3930747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 3].length) (baseStart_3930747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930747 prefixEnd_3930747 := by exact prefixLift 3930747
  have htrace : WordTrace (prefixWord ++ tailWord_3930747) baseStart_3930747 baseEnd_3930747 := by
    simpa [prefixWord, tailWord_3930747, baseEnd_3930747] using wordTrace_append hprefix tailTrace_3930747
  have hstable : (prefixWord ++ tailWord_3930747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930747).length < 2 ^ (prefixWord ++ tailWord_3930747).sum := by decide
  have hdescent : baseEnd_3930747 < baseStart_3930747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930775 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 2, 7]
def baseStart_3930775 : Nat := 118140960795 + 3930775 * 2 ^ 59
def prefixEnd_3930775 : Nat := 4983230072969 + 3 ^ 40 * 3930775 * 2
def baseEnd_3930775 : Nat := 1345584613117975705623467

theorem tailTrace_3930775 : CollatzResearch.WordTrace tailWord_3930775 prefixEnd_3930775 1345584613117975705623467 := by
  unfold tailWord_3930775
  simp only [CollatzResearch.WordTrace]
  refine ⟨143367142334480972768361779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95578094889653981845574519 143367142334480972768361779)
  ·
    refine ⟨215050713501721459152542669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143367142334480972768361779 215050713501721459152542669)
    ·
      refine ⟨80644017563145547182203501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215050713501721459152542669 80644017563145547182203501)
      ·
        refine ⟨30241506586179580193326313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80644017563145547182203501 30241506586179580193326313)
        ·
          refine ⟨22681129939634685144994735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30241506586179580193326313 22681129939634685144994735)
          ·
            refine ⟨34021694909452027717492103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22681129939634685144994735 34021694909452027717492103)
            ·
              refine ⟨51032542364178041576238155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34021694909452027717492103 51032542364178041576238155)
              ·
                refine ⟨76548813546267062364357233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51032542364178041576238155 76548813546267062364357233)
                ·
                  refine ⟨57411610159700296773267925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76548813546267062364357233 57411610159700296773267925)
                  ·
                    refine ⟨1345584613117975705623467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57411610159700296773267925 1345584613117975705623467)
                    ·
                      rfl

theorem cell22_3930775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_3930775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930775 prefixEnd_3930775 := by exact prefixLift 3930775
  have htrace : WordTrace (prefixWord ++ tailWord_3930775) baseStart_3930775 baseEnd_3930775 := by
    simpa [prefixWord, tailWord_3930775, baseEnd_3930775] using wordTrace_append hprefix tailTrace_3930775
  have hstable : (prefixWord ++ tailWord_3930775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930775).length < 2 ^ (prefixWord ++ tailWord_3930775).sum := by decide
  have hdescent : baseEnd_3930775 < baseStart_3930775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930903 : List Nat := [1, 1, 3, 4, 3, 2, 2, 1, 1, 4]
def baseStart_3930903 : Nat := 118140960795 + 3930903 * 2 ^ 59
def prefixEnd_3930903 : Nat := 4983230072969 + 3 ^ 40 * 3930903 * 2
def baseEnd_3930903 : Nat := 1345628430133826038423075

theorem tailTrace_3930903 : CollatzResearch.WordTrace tailWord_3930903 prefixEnd_3930903 1345628430133826038423075 := by
  unfold tailWord_3930903
  simp only [CollatzResearch.WordTrace]
  refine ⟨143371810878017250629021363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95581207252011500419347575 143371810878017250629021363)
  ·
    refine ⟨215057716317025875943532045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143371810878017250629021363 215057716317025875943532045)
    ·
      refine ⟨80646643618884703478824517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215057716317025875943532045 80646643618884703478824517)
      ·
        refine ⟨15121245678540881902279597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80646643618884703478824517 15121245678540881902279597)
        ·
          refine ⟨5670467129452830713354849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15121245678540881902279597 5670467129452830713354849)
          ·
            refine ⟨4252850347089623035016137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5670467129452830713354849 4252850347089623035016137)
            ·
              refine ⟨3189637760317217276262103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4252850347089623035016137 3189637760317217276262103)
              ·
                refine ⟨4784456640475825914393155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3189637760317217276262103 4784456640475825914393155)
                ·
                  refine ⟨7176684960713738871589733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4784456640475825914393155 7176684960713738871589733)
                  ·
                    refine ⟨1345628430133826038423075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7176684960713738871589733 1345628430133826038423075)
                    ·
                      rfl

theorem cell22_3930903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 1, 4].length) (baseStart_3930903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930903 prefixEnd_3930903 := by exact prefixLift 3930903
  have htrace : WordTrace (prefixWord ++ tailWord_3930903) baseStart_3930903 baseEnd_3930903 := by
    simpa [prefixWord, tailWord_3930903, baseEnd_3930903] using wordTrace_append hprefix tailTrace_3930903
  have hstable : (prefixWord ++ tailWord_3930903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930903).length < 2 ^ (prefixWord ++ tailWord_3930903).sum := by decide
  have hdescent : baseEnd_3930903 < baseStart_3930903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930912 : List Nat := [2, 1, 1, 5, 1, 3, 9]
def baseStart_3930912 : Nat := 118140960795 + 3930912 * 2 ^ 59
def prefixEnd_3930912 : Nat := 4983230072969 + 3 ^ 40 * 3930912 * 2
def baseEnd_3930912 : Nat := 49838204111768630183261

theorem tailTrace_3930912 : CollatzResearch.WordTrace tailWord_3930912 prefixEnd_3930912 49838204111768630183261 := by
  unfold tailWord_3930912
  simp only [CollatzResearch.WordTrace]
  refine ⟨71686069567492322583049495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95581426089989763444065993 71686069567492322583049495)
  ·
    refine ⟨107529104351238483874574243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71686069567492322583049495 107529104351238483874574243)
    ·
      refine ⟨161293656526857725811861365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107529104351238483874574243 161293656526857725811861365)
      ·
        refine ⟨15121280299392911794862003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161293656526857725811861365 15121280299392911794862003)
        ·
          refine ⟨22681920449089367692293005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15121280299392911794862003 22681920449089367692293005)
          ·
            refine ⟨8505720168408512884609877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22681920449089367692293005 8505720168408512884609877)
            ·
              refine ⟨49838204111768630183261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8505720168408512884609877 49838204111768630183261)
              ·
                rfl

theorem cell22_3930912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 9].length) (baseStart_3930912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930912 prefixEnd_3930912 := by exact prefixLift 3930912
  have htrace : WordTrace (prefixWord ++ tailWord_3930912) baseStart_3930912 baseEnd_3930912 := by
    simpa [prefixWord, tailWord_3930912, baseEnd_3930912] using wordTrace_append hprefix tailTrace_3930912
  have hstable : (prefixWord ++ tailWord_3930912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930912).length < 2 ^ (prefixWord ++ tailWord_3930912).sum := by decide
  have hdescent : baseEnd_3930912 < baseStart_3930912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930916 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 4, 3]
def baseStart_3930916 : Nat := 118140960795 + 3930916 * 2 ^ 59
def prefixEnd_3930916 : Nat := 4983230072969 + 3 ^ 40 * 3930916 * 2
def baseEnd_3930916 : Nat := 1345632880299498337848035

theorem tailTrace_3930916 : CollatzResearch.WordTrace tailWord_3930916 prefixEnd_3930916 1345632880299498337848035 := by
  unfold tailWord_3930916
  simp only [CollatzResearch.WordTrace]
  refine ⟨71686142513485076924622301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95581523351313435899496401 71686142513485076924622301)
  ·
    refine ⟨26882303442556903846733363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71686142513485076924622301 26882303442556903846733363)
    ·
      refine ⟨40323455163835355770100045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26882303442556903846733363 40323455163835355770100045)
      ·
        refine ⟨15121295686438258413787517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40323455163835355770100045 15121295686438258413787517)
        ·
          refine ⟨5670485882414346905170319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15121295686438258413787517 5670485882414346905170319)
          ·
            refine ⟨8505728823621520357755479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5670485882414346905170319 8505728823621520357755479)
            ·
              refine ⟨12758593235432280536633219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8505728823621520357755479 12758593235432280536633219)
              ·
                refine ⟨19137889853148420804949829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12758593235432280536633219 19137889853148420804949829)
                ·
                  refine ⟨3588354347465328900928093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19137889853148420804949829 3588354347465328900928093)
                  ·
                    refine ⟨1345632880299498337848035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3588354347465328900928093 1345632880299498337848035)
                    ·
                      rfl

theorem cell22_3930916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_3930916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930916 prefixEnd_3930916 := by exact prefixLift 3930916
  have htrace : WordTrace (prefixWord ++ tailWord_3930916) baseStart_3930916 baseEnd_3930916 := by
    simpa [prefixWord, tailWord_3930916, baseEnd_3930916] using wordTrace_append hprefix tailTrace_3930916
  have hstable : (prefixWord ++ tailWord_3930916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930916).length < 2 ^ (prefixWord ++ tailWord_3930916).sum := by decide
  have hdescent : baseEnd_3930916 < baseStart_3930916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930933 : List Nat := [1, 3, 3, 1, 3, 2, 3, 1, 2, 3]
def baseStart_3930933 : Nat := 118140960795 + 3930933 * 2 ^ 59
def prefixEnd_3930933 : Nat := 4983230072969 + 3 ^ 40 * 3930933 * 2
def baseEnd_3930933 : Nat := 1345638699746915960172983

theorem tailTrace_3930933 : CollatzResearch.WordTrace tailWord_3930933 prefixEnd_3930933 1345638699746915960172983 := by
  unfold tailWord_3930933
  simp only [CollatzResearch.WordTrace]
  refine ⟨143372905067908565752613453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95581936711939043835075635 143372905067908565752613453)
  ·
    refine ⟨53764839400465712157230045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143372905067908565752613453 53764839400465712157230045)
    ·
      refine ⟨20161814775174642058961267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53764839400465712157230045 20161814775174642058961267)
      ·
        refine ⟨30242722162761963088441901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20161814775174642058961267 30242722162761963088441901)
        ·
          refine ⟨11341020811035736158165713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30242722162761963088441901 11341020811035736158165713)
          ·
            refine ⟨8505765608276802118624285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11341020811035736158165713 8505765608276802118624285)
            ·
              refine ⟨3189662103103800794484107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8505765608276802118624285 3189662103103800794484107)
              ·
                refine ⟨4784493154655701191726161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3189662103103800794484107 4784493154655701191726161)
                ·
                  refine ⟨3588369865991775893794621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4784493154655701191726161 3588369865991775893794621)
                  ·
                    refine ⟨1345638699746915960172983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3588369865991775893794621 1345638699746915960172983)
                    ·
                      rfl

theorem cell22_3930933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_3930933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3930933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3930933 prefixEnd_3930933 := by exact prefixLift 3930933
  have htrace : WordTrace (prefixWord ++ tailWord_3930933) baseStart_3930933 baseEnd_3930933 := by
    simpa [prefixWord, tailWord_3930933, baseEnd_3930933] using wordTrace_append hprefix tailTrace_3930933
  have hstable : (prefixWord ++ tailWord_3930933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930933).length < 2 ^ (prefixWord ++ tailWord_3930933).sum := by decide
  have hdescent : baseEnd_3930933 < baseStart_3930933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931002 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 8]
def baseStart_3931002 : Nat := 118140960795 + 3931002 * 2 ^ 59
def prefixEnd_3931002 : Nat := 4983230072969 + 3 ^ 40 * 3931002 * 2
def baseEnd_3931002 : Nat := 448554106619007593399257

theorem tailTrace_3931002 : CollatzResearch.WordTrace tailWord_3931002 prefixEnd_3931002 448554106619007593399257 := by
  unfold tailWord_3931002
  simp only [CollatzResearch.WordTrace]
  refine ⟨35843855426164647634218815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95583614469772393691250173 35843855426164647634218815)
  ·
    refine ⟨53765783139246971451328223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35843855426164647634218815 53765783139246971451328223)
    ·
      refine ⟨80648674708870457176992335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53765783139246971451328223 80648674708870457176992335)
      ·
        refine ⟨120973012063305685765488503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80648674708870457176992335 120973012063305685765488503)
        ·
          refine ⟨181459518094958528648232755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120973012063305685765488503 181459518094958528648232755)
          ·
            refine ⟨272189277142437792972349133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181459518094958528648232755 272189277142437792972349133)
            ·
              refine ⟨102070978928414172364630925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272189277142437792972349133 102070978928414172364630925)
              ·
                refine ⟨38276617098155314636736597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102070978928414172364630925 38276617098155314636736597)
                ·
                  refine ⟨448554106619007593399257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38276617098155314636736597 448554106619007593399257)
                  ·
                    rfl

theorem cell22_3931002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_3931002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931002 prefixEnd_3931002 := by exact prefixLift 3931002
  have htrace : WordTrace (prefixWord ++ tailWord_3931002) baseStart_3931002 baseEnd_3931002 := by
    simpa [prefixWord, tailWord_3931002, baseEnd_3931002] using wordTrace_append hprefix tailTrace_3931002
  have hstable : (prefixWord ++ tailWord_3931002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931002).length < 2 ^ (prefixWord ++ tailWord_3931002).sum := by decide
  have hdescent : baseEnd_3931002 < baseStart_3931002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931053 : List Nat := [1, 5, 2, 3, 1, 1, 1, 2, 6]
def baseStart_3931053 : Nat := 118140960795 + 3931053 * 2 ^ 59
def prefixEnd_3931053 : Nat := 4983230072969 + 3 ^ 40 * 3931053 * 2
def baseEnd_3931053 : Nat := 448559926066425215724205

theorem tailTrace_3931053 : CollatzResearch.WordTrace tailWord_3931053 prefixEnd_3931053 448559926066425215724205 := by
  unfold tailWord_3931053
  simp only [CollatzResearch.WordTrace]
  refine ⟨143377281827473826246981813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95584854551649217497987875 143377281827473826246981813)
  ·
    refine ⟨13441620171325671210654545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143377281827473826246981813 13441620171325671210654545)
    ·
      refine ⟨10081215128494253407990909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13441620171325671210654545 10081215128494253407990909)
      ·
        refine ⟨3780455673185345027996591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10081215128494253407990909 3780455673185345027996591)
        ·
          refine ⟨5670683509778017541994887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3780455673185345027996591 5670683509778017541994887)
          ·
            refine ⟨8506025264667026312992331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5670683509778017541994887 8506025264667026312992331)
            ·
              refine ⟨12759037897000539469488497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8506025264667026312992331 12759037897000539469488497)
              ·
                refine ⟨9569278422750404602116373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12759037897000539469488497 9569278422750404602116373)
                ·
                  refine ⟨448559926066425215724205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9569278422750404602116373 448559926066425215724205)
                  ·
                    rfl

theorem cell22_3931053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_3931053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931053 prefixEnd_3931053 := by exact prefixLift 3931053
  have htrace : WordTrace (prefixWord ++ tailWord_3931053) baseStart_3931053 baseEnd_3931053 := by
    simpa [prefixWord, tailWord_3931053, baseEnd_3931053] using wordTrace_append hprefix tailTrace_3931053
  have hstable : (prefixWord ++ tailWord_3931053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931053).length < 2 ^ (prefixWord ++ tailWord_3931053).sum := by decide
  have hdescent : baseEnd_3931053 < baseStart_3931053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931096 : List Nat := [2, 1, 2, 2, 2, 3, 1, 3, 3, 3]
def baseStart_3931096 : Nat := 118140960795 + 3931096 * 2 ^ 59
def prefixEnd_3931096 : Nat := 4983230072969 + 3 ^ 40 * 3931096 * 2
def baseEnd_3931096 : Nat := 1345694497978037868347483

theorem tailTrace_3931096 : CollatzResearch.WordTrace tailWord_3931096 prefixEnd_3931096 1345694497978037868347483 := by
  unfold tailWord_3931096
  simp only [CollatzResearch.WordTrace]
  refine ⟨71689425083159022295398571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95585900110878696393864761 71689425083159022295398571)
  ·
    refine ⟨107534137624738533443097857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71689425083159022295398571 107534137624738533443097857)
    ·
      refine ⟨80650603218553900082323393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107534137624738533443097857 80650603218553900082323393)
      ·
        refine ⟨60487952413915425061742545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80650603218553900082323393 60487952413915425061742545)
        ·
          refine ⟨45365964310436568796306909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60487952413915425061742545 45365964310436568796306909)
          ·
            refine ⟨17012236616413713298615091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45365964310436568796306909 17012236616413713298615091)
            ·
              refine ⟨25518354924620569947922637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17012236616413713298615091 25518354924620569947922637)
              ·
                refine ⟨9569383096732713730470989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25518354924620569947922637 9569383096732713730470989)
                ·
                  refine ⟨3588518661274767648926621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9569383096732713730470989 3588518661274767648926621)
                  ·
                    refine ⟨1345694497978037868347483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3588518661274767648926621 1345694497978037868347483)
                    ·
                      rfl

theorem cell22_3931096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_3931096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931096 prefixEnd_3931096 := by exact prefixLift 3931096
  have htrace : WordTrace (prefixWord ++ tailWord_3931096) baseStart_3931096 baseEnd_3931096 := by
    simpa [prefixWord, tailWord_3931096, baseEnd_3931096] using wordTrace_append hprefix tailTrace_3931096
  have hstable : (prefixWord ++ tailWord_3931096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931096).length < 2 ^ (prefixWord ++ tailWord_3931096).sum := by decide
  have hdescent : baseEnd_3931096 < baseStart_3931096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931126 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_3931126 : Nat := 118140960795 + 3931126 * 2 ^ 59
def prefixEnd_3931126 : Nat := 4983230072969 + 3 ^ 40 * 3931126 * 2
def baseEnd_3931126 : Nat := 448568255863709263365797

theorem tailTrace_3931126 : CollatzResearch.WordTrace tailWord_3931126 prefixEnd_3931126 448568255863709263365797 := by
  unfold tailWord_3931126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8961246522263084982149327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95586629570806239809592821 8961246522263084982149327)
  ·
    refine ⟨13441869783394627473223991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8961246522263084982149327 13441869783394627473223991)
    ·
      refine ⟨20162804675091941209835987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13441869783394627473223991 20162804675091941209835987)
      ·
        refine ⟨30244207012637911814753981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20162804675091941209835987 30244207012637911814753981)
        ·
          refine ⟨11341577629739216930532743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30244207012637911814753981 11341577629739216930532743)
          ·
            refine ⟨17012366444608825395799115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11341577629739216930532743 17012366444608825395799115)
            ·
              refine ⟨25518549666913238093698673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17012366444608825395799115 25518549666913238093698673)
              ·
                refine ⟨19138912250184928570274005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25518549666913238093698673 19138912250184928570274005)
                ·
                  refine ⟨448568255863709263365797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19138912250184928570274005 448568255863709263365797)
                  ·
                    rfl

theorem cell22_3931126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_3931126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931126 prefixEnd_3931126 := by exact prefixLift 3931126
  have htrace : WordTrace (prefixWord ++ tailWord_3931126) baseStart_3931126 baseEnd_3931126 := by
    simpa [prefixWord, tailWord_3931126, baseEnd_3931126] using wordTrace_append hprefix tailTrace_3931126
  have hstable : (prefixWord ++ tailWord_3931126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931126).length < 2 ^ (prefixWord ++ tailWord_3931126).sum := by decide
  have hdescent : baseEnd_3931126 < baseStart_3931126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931139 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 7, 4]
def baseStart_3931139 : Nat := 118140960795 + 3931139 * 2 ^ 59
def prefixEnd_3931139 : Nat := 4983230072969 + 3 ^ 40 * 3931139 * 2
def baseEnd_3931139 : Nat := 1345709217756800089522351

theorem tailTrace_3931139 : CollatzResearch.WordTrace tailWord_3931139 prefixEnd_3931139 1345709217756800089522351 := by
  unfold tailWord_3931139
  simp only [CollatzResearch.WordTrace]
  refine ⟨143380418505162262934612471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95586945670108175289741647 143380418505162262934612471)
  ·
    refine ⟨215070627757743394401918707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143380418505162262934612471 215070627757743394401918707)
    ·
      refine ⟨322605941636615091602878061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215070627757743394401918707 322605941636615091602878061)
      ·
        refine ⟨120977228113730659351079273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322605941636615091602878061 120977228113730659351079273)
        ·
          refine ⟨90732921085297994513309455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120977228113730659351079273 90732921085297994513309455)
          ·
            refine ⟨136099381627946991769964183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90732921085297994513309455 136099381627946991769964183)
            ·
              refine ⟨204149072441920487654946275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136099381627946991769964183 204149072441920487654946275)
              ·
                refine ⟨306223608662880731482419413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204149072441920487654946275 306223608662880731482419413)
                ·
                  refine ⟨7177115828036267144119205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 306223608662880731482419413 7177115828036267144119205)
                  ·
                    refine ⟨1345709217756800089522351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7177115828036267144119205 1345709217756800089522351)
                    ·
                      rfl

theorem cell22_3931139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 4].length) (baseStart_3931139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931139 prefixEnd_3931139 := by exact prefixLift 3931139
  have htrace : WordTrace (prefixWord ++ tailWord_3931139) baseStart_3931139 baseEnd_3931139 := by
    simpa [prefixWord, tailWord_3931139, baseEnd_3931139] using wordTrace_append hprefix tailTrace_3931139
  have hstable : (prefixWord ++ tailWord_3931139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931139).length < 2 ^ (prefixWord ++ tailWord_3931139).sum := by decide
  have hdescent : baseEnd_3931139 < baseStart_3931139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931186 : List Nat := [3, 2, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_3931186 : Nat := 118140960795 + 3931186 * 2 ^ 59
def prefixEnd_3931186 : Nat := 4983230072969 + 3 ^ 40 * 3931186 * 2
def baseEnd_3931186 : Nat := 1345725306817307633597207

theorem tailTrace_3931186 : CollatzResearch.WordTrace tailWord_3931186 prefixEnd_3931186 1345725306817307633597207 := by
  unfold tailWord_3931186
  simp only [CollatzResearch.WordTrace]
  refine ⟨35845533183997997490393353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95588088490661326641048941 35845533183997997490393353)
  ·
    refine ⟨26884149887998498117795015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35845533183997997490393353 26884149887998498117795015)
    ·
      refine ⟨40326224831997747176692523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26884149887998498117795015 40326224831997747176692523)
      ·
        refine ⟨60489337247996620765038785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40326224831997747176692523 60489337247996620765038785)
        ·
          refine ⟨45367002935997465573779089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60489337247996620765038785 45367002935997465573779089)
          ·
            refine ⟨34025252201998099180334317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45367002935997465573779089 34025252201998099180334317)
            ·
              refine ⟨12759469575749287192625369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34025252201998099180334317 12759469575749287192625369)
              ·
                refine ⟨9569602181811965394469027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12759469575749287192625369 9569602181811965394469027)
                ·
                  refine ⟨14354403272717948091703541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9569602181811965394469027 14354403272717948091703541)
                  ·
                    refine ⟨1345725306817307633597207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14354403272717948091703541 1345725306817307633597207)
                    ·
                      rfl

theorem cell22_3931186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_3931186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931186 prefixEnd_3931186 := by exact prefixLift 3931186
  have htrace : WordTrace (prefixWord ++ tailWord_3931186) baseStart_3931186 baseEnd_3931186 := by
    simpa [prefixWord, tailWord_3931186, baseEnd_3931186] using wordTrace_append hprefix tailTrace_3931186
  have hstable : (prefixWord ++ tailWord_3931186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931186).length < 2 ^ (prefixWord ++ tailWord_3931186).sum := by decide
  have hdescent : baseEnd_3931186 < baseStart_3931186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931203 : List Nat := [1, 1, 1, 3, 1, 2, 6, 2, 2, 3]
def baseStart_3931203 : Nat := 118140960795 + 3931203 * 2 ^ 59
def prefixEnd_3931203 : Nat := 4983230072969 + 3 ^ 40 * 3931203 * 2
def baseEnd_3931203 : Nat := 1345731126264725255922155

theorem tailTrace_3931203 : CollatzResearch.WordTrace tailWord_3931203 prefixEnd_3931203 1345731126264725255922155 := by
  unfold tailWord_3931203
  simp only [CollatzResearch.WordTrace]
  refine ⟨143382752776930401864942263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95588501851286934576628175 143382752776930401864942263)
  ·
    refine ⟨215074129165395602797413395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143382752776930401864942263 215074129165395602797413395)
    ·
      refine ⟨322611193748093404196120093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215074129165395602797413395 322611193748093404196120093)
      ·
        refine ⟨120979197655535026573545035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322611193748093404196120093 120979197655535026573545035)
        ·
          refine ⟨181468796483302539860317553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120979197655535026573545035 181468796483302539860317553)
          ·
            refine ⟨136101597362476904895238165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181468796483302539860317553 136101597362476904895238165)
            ·
              refine ⟨6379762376366104916964289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136101597362476904895238165 6379762376366104916964289)
              ·
                refine ⟨4784821782274578687723217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6379762376366104916964289 4784821782274578687723217)
                ·
                  refine ⟨3588616336705934015792413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4784821782274578687723217 3588616336705934015792413)
                  ·
                    refine ⟨1345731126264725255922155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3588616336705934015792413 1345731126264725255922155)
                    ·
                      rfl

theorem cell22_3931203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 3].length) (baseStart_3931203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931203 prefixEnd_3931203 := by exact prefixLift 3931203
  have htrace : WordTrace (prefixWord ++ tailWord_3931203) baseStart_3931203 baseEnd_3931203 := by
    simpa [prefixWord, tailWord_3931203, baseEnd_3931203] using wordTrace_append hprefix tailTrace_3931203
  have hstable : (prefixWord ++ tailWord_3931203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931203).length < 2 ^ (prefixWord ++ tailWord_3931203).sum := by decide
  have hdescent : baseEnd_3931203 < baseStart_3931203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931261 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 7]
def baseStart_3931261 : Nat := 118140960795 + 3931261 * 2 ^ 59
def prefixEnd_3931261 : Nat := 4983230072969 + 3 ^ 40 * 3931261 * 2
def baseEnd_3931261 : Nat := 448583660283344145990659

theorem tailTrace_3931261 : CollatzResearch.WordTrace tailWord_3931261 prefixEnd_3931261 448583660283344145990659 := by
  unfold tailWord_3931261
  simp only [CollatzResearch.WordTrace]
  refine ⟨143384868210720277770553637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95589912140480185180369091 143384868210720277770553637)
  ·
    refine ⟨26884662789510052081978807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143384868210720277770553637 26884662789510052081978807)
    ·
      refine ⟨40326994184265078122968211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26884662789510052081978807 40326994184265078122968211)
      ·
        refine ⟨60490491276397617184452317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40326994184265078122968211 60490491276397617184452317)
        ·
          refine ⟨22683934228649106444169619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60490491276397617184452317 22683934228649106444169619)
          ·
            refine ⟨34025901342973659666254429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22683934228649106444169619 34025901342973659666254429)
            ·
              refine ⟨12759713003615122374845411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34025901342973659666254429 12759713003615122374845411)
              ·
                refine ⟨19139569505422683562268117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12759713003615122374845411 19139569505422683562268117)
                ·
                  refine ⟨448583660283344145990659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19139569505422683562268117 448583660283344145990659)
                  ·
                    rfl

theorem cell22_3931261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_3931261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931261 prefixEnd_3931261 := by exact prefixLift 3931261
  have htrace : WordTrace (prefixWord ++ tailWord_3931261) baseStart_3931261 baseEnd_3931261 := by
    simpa [prefixWord, tailWord_3931261, baseEnd_3931261] using wordTrace_append hprefix tailTrace_3931261
  have hstable : (prefixWord ++ tailWord_3931261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931261).length < 2 ^ (prefixWord ++ tailWord_3931261).sum := by decide
  have hdescent : baseEnd_3931261 < baseStart_3931261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931265 : List Nat := [1, 2, 4, 2, 2, 2, 2, 1, 3, 3]
def baseStart_3931265 : Nat := 118140960795 + 3931265 * 2 ^ 59
def prefixEnd_3931265 : Nat := 4983230072969 + 3 ^ 40 * 3931265 * 2
def baseEnd_3931265 : Nat := 1345752350131777760871965

theorem tailTrace_3931265 : CollatzResearch.WordTrace tailWord_3931265 prefixEnd_3931265 1345752350131777760871965 := by
  unfold tailWord_3931265
  simp only [CollatzResearch.WordTrace]
  refine ⟨143385014102705786453699249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95590009401803857635799499 143385014102705786453699249)
  ·
    refine ⟨107538760577029339840274437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143385014102705786453699249 107538760577029339840274437)
    ·
      refine ⟨20163517608193001220051457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107538760577029339840274437 20163517608193001220051457)
      ·
        refine ⟨15122638206144750915038593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20163517608193001220051457 15122638206144750915038593)
        ·
          refine ⟨11341978654608563186278945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15122638206144750915038593 11341978654608563186278945)
          ·
            refine ⟨8506483990956422389709209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11341978654608563186278945 8506483990956422389709209)
            ·
              refine ⟨6379862993217316792281907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8506483990956422389709209 6379862993217316792281907)
              ·
                refine ⟨9569794489825975188422861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6379862993217316792281907 9569794489825975188422861)
                ·
                  refine ⟨3588672933684740695658573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9569794489825975188422861 3588672933684740695658573)
                  ·
                    refine ⟨1345752350131777760871965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3588672933684740695658573 1345752350131777760871965)
                    ·
                      rfl

theorem cell22_3931265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_3931265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931265 prefixEnd_3931265 := by exact prefixLift 3931265
  have htrace : WordTrace (prefixWord ++ tailWord_3931265) baseStart_3931265 baseEnd_3931265 := by
    simpa [prefixWord, tailWord_3931265, baseEnd_3931265] using wordTrace_append hprefix tailTrace_3931265
  have hstable : (prefixWord ++ tailWord_3931265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931265).length < 2 ^ (prefixWord ++ tailWord_3931265).sum := by decide
  have hdescent : baseEnd_3931265 < baseStart_3931265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931336 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 3, 6]
def baseStart_3931336 : Nat := 118140960795 + 3931336 * 2 ^ 59
def prefixEnd_3931336 : Nat := 4983230072969 + 3 ^ 40 * 3931336 * 2
def baseEnd_3931336 : Nat := 1345776654882757242346747

theorem tailTrace_3931336 : CollatzResearch.WordTrace tailWord_3931336 prefixEnd_3931336 1345776654882757242346747 := by
  unfold tailWord_3931336
  simp only [CollatzResearch.WordTrace]
  refine ⟨71693801842724282789766931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95591735790299043719689241 71693801842724282789766931)
  ·
    refine ⟨107540702764086424184650397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71693801842724282789766931 107540702764086424184650397)
    ·
      refine ⟨40327763536532409069243899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107540702764086424184650397 40327763536532409069243899)
      ·
        refine ⟨60491645304798613603865849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40327763536532409069243899 60491645304798613603865849)
        ·
          refine ⟨45368733978598960202899387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60491645304798613603865849 45368733978598960202899387)
          ·
            refine ⟨68053100967898440304349081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45368733978598960202899387 68053100967898440304349081)
            ·
              refine ⟨51039825725923830228261811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68053100967898440304349081 51039825725923830228261811)
              ·
                refine ⟨76559738588885745342392717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51039825725923830228261811 76559738588885745342392717)
                ·
                  refine ⟨28709901970832154503397269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76559738588885745342392717 28709901970832154503397269)
                  ·
                    refine ⟨1345776654882757242346747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28709901970832154503397269 1345776654882757242346747)
                    ·
                      rfl

theorem cell22_3931336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_3931336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931336 prefixEnd_3931336 := by exact prefixLift 3931336
  have htrace : WordTrace (prefixWord ++ tailWord_3931336) baseStart_3931336 baseEnd_3931336 := by
    simpa [prefixWord, tailWord_3931336, baseEnd_3931336] using wordTrace_append hprefix tailTrace_3931336
  have hstable : (prefixWord ++ tailWord_3931336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931336).length < 2 ^ (prefixWord ++ tailWord_3931336).sum := by decide
  have hdescent : baseEnd_3931336 < baseStart_3931336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
