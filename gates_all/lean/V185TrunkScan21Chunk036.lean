import V185TrunkScan21Chunk035

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_435176 : List Nat := [2, 1, 4, 1, 1, 1, 2, 4, 5]
def baseStart_435176 : Nat := 118140960795 + 435176 * 2 ^ 59
def prefixEnd_435176 : Nat := 4983230072969 + 3 ^ 40 * 435176 * 2
def baseEnd_435176 : Nat := 99313092133819824710519

theorem tailTrace_435176 : CollatzResearch.WordTrace tailWord_435176 prefixEnd_435176 99313092133819824710519 := by
  unfold tailWord_435176
  simp only [CollatzResearch.WordTrace]
  refine ⟨7936086335719574494410691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10581448447626099325880921 7936086335719574494410691)
  ·
    refine ⟨11904129503579361741616037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7936086335719574494410691 11904129503579361741616037)
    ·
      refine ⟨2232024281921130326553007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11904129503579361741616037 2232024281921130326553007)
      ·
        refine ⟨3348036422881695489829511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2232024281921130326553007 3348036422881695489829511)
        ·
          refine ⟨5022054634322543234744267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3348036422881695489829511 5022054634322543234744267)
          ·
            refine ⟨7533081951483814852116401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5022054634322543234744267 7533081951483814852116401)
            ·
              refine ⟨5649811463612861139087301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7533081951483814852116401 5649811463612861139087301)
              ·
                refine ⟨1059339649427411463578869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5649811463612861139087301 1059339649427411463578869)
                ·
                  refine ⟨99313092133819824710519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1059339649427411463578869 99313092133819824710519)
                  ·
                    rfl

theorem cell21_435176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_435176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435176 prefixEnd_435176 := by exact prefixLift 435176
  have htrace : WordTrace (prefixWord ++ tailWord_435176) baseStart_435176 baseEnd_435176 := by
    simpa [prefixWord, tailWord_435176, baseEnd_435176] using wordTrace_append hprefix tailTrace_435176
  have hstable : (prefixWord ++ tailWord_435176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435176).length < 2 ^ (prefixWord ++ tailWord_435176).sum := by decide
  have hdescent : baseEnd_435176 < baseStart_435176 := by decide
  rcases family_descends (prefixWord ++ tailWord_435176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435193 : List Nat := [1, 2, 1, 3, 1, 3, 2, 5, 3]
def baseStart_435193 : Nat := 118140960795 + 435193 * 2 ^ 59
def prefixEnd_435193 : Nat := 4983230072969 + 3 ^ 40 * 435193 * 2
def baseEnd_435193 : Nat := 99316971765431572927151

theorem tailTrace_435193 : CollatzResearch.WordTrace tailWord_435193 prefixEnd_435193 99316971765431572927151 := by
  unfold tailWord_435193
  simp only [CollatzResearch.WordTrace]
  refine ⟨15872792712377560892190233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10581861808251707261460155 15872792712377560892190233)
  ·
    refine ⟨11904594534283170669142675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15872792712377560892190233 11904594534283170669142675)
    ·
      refine ⟨17856891801424756003714013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11904594534283170669142675 17856891801424756003714013)
      ·
        refine ⟨6696334425534283501392755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17856891801424756003714013 6696334425534283501392755)
        ·
          refine ⟨10044501638301425252089133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6696334425534283501392755 10044501638301425252089133)
          ·
            refine ⟨3766688114363034469533425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10044501638301425252089133 3766688114363034469533425)
            ·
              refine ⟨2825016085772275852150069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3766688114363034469533425 2825016085772275852150069)
              ·
                refine ⟨264845258041150861139069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2825016085772275852150069 264845258041150861139069)
                ·
                  refine ⟨99316971765431572927151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264845258041150861139069 99316971765431572927151)
                  ·
                    rfl

theorem cell21_435193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 3].length) (baseStart_435193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435193 prefixEnd_435193 := by exact prefixLift 435193
  have htrace : WordTrace (prefixWord ++ tailWord_435193) baseStart_435193 baseEnd_435193 := by
    simpa [prefixWord, tailWord_435193, baseEnd_435193] using wordTrace_append hprefix tailTrace_435193
  have hstable : (prefixWord ++ tailWord_435193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435193).length < 2 ^ (prefixWord ++ tailWord_435193).sum := by decide
  have hdescent : baseEnd_435193 < baseStart_435193 := by decide
  rcases family_descends (prefixWord ++ tailWord_435193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435202 : List Nat := [3, 4, 1, 3, 2, 1, 2, 2, 3]
def baseStart_435202 : Nat := 118140960795 + 435202 * 2 ^ 59
def prefixEnd_435202 : Nat := 4983230072969 + 3 ^ 40 * 435202 * 2
def baseEnd_435202 : Nat := 99319025688049557277133

theorem tailTrace_435202 : CollatzResearch.WordTrace tailWord_435202 prefixEnd_435202 99319025688049557277133 := by
  unfold tailWord_435202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3968280242336238857316965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10582080646229970286178573 3968280242336238857316965)
  ·
    refine ⟨744052545438044785746931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3968280242336238857316965 744052545438044785746931)
    ·
      refine ⟨1116078818157067178620397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 744052545438044785746931 1116078818157067178620397)
      ·
        refine ⟨418529556808900191982649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1116078818157067178620397 418529556808900191982649)
        ·
          refine ⟨313897167606675143986987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418529556808900191982649 313897167606675143986987)
          ·
            refine ⟨470845751410012715980481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313897167606675143986987 470845751410012715980481)
            ·
              refine ⟨353134313557509536985361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470845751410012715980481 353134313557509536985361)
              ·
                refine ⟨264850735168132152739021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353134313557509536985361 264850735168132152739021)
                ·
                  refine ⟨99319025688049557277133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264850735168132152739021 99319025688049557277133)
                  ·
                    rfl

theorem cell21_435202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_435202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435202 prefixEnd_435202 := by exact prefixLift 435202
  have htrace : WordTrace (prefixWord ++ tailWord_435202) baseStart_435202 baseEnd_435202 := by
    simpa [prefixWord, tailWord_435202, baseEnd_435202] using wordTrace_append hprefix tailTrace_435202
  have hstable : (prefixWord ++ tailWord_435202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435202).length < 2 ^ (prefixWord ++ tailWord_435202).sum := by decide
  have hdescent : baseEnd_435202 < baseStart_435202 := by decide
  rcases family_descends (prefixWord ++ tailWord_435202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435210 : List Nat := [3, 1, 2, 2, 3, 2, 1, 4, 3]
def baseStart_435210 : Nat := 118140960795 + 435210 * 2 ^ 59
def prefixEnd_435210 : Nat := 4983230072969 + 3 ^ 40 * 435210 * 2
def baseEnd_435210 : Nat := 99320851397043321143783

theorem tailTrace_435210 : CollatzResearch.WordTrace tailWord_435210 prefixEnd_435210 99320851397043321143783 := by
  unfold tailWord_435210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3968353188328993198889771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10582275168877315197039389 3968353188328993198889771)
  ·
    refine ⟨5952529782493489798334657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3968353188328993198889771 5952529782493489798334657)
    ·
      refine ⟨4464397336870117348750993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5952529782493489798334657 4464397336870117348750993)
      ·
        refine ⟨3348298002652588011563245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4464397336870117348750993 3348298002652588011563245)
        ·
          refine ⟨1255611750994720504336217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3348298002652588011563245 1255611750994720504336217)
          ·
            refine ⟨941708813246040378252163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1255611750994720504336217 941708813246040378252163)
            ·
              refine ⟨1412563219869060567378245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941708813246040378252163 1412563219869060567378245)
              ·
                refine ⟨264855603725448856383421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1412563219869060567378245 264855603725448856383421)
                ·
                  refine ⟨99320851397043321143783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264855603725448856383421 99320851397043321143783)
                  ·
                    rfl

theorem cell21_435210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_435210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435210 prefixEnd_435210 := by exact prefixLift 435210
  have htrace : WordTrace (prefixWord ++ tailWord_435210) baseStart_435210 baseEnd_435210 := by
    simpa [prefixWord, tailWord_435210, baseEnd_435210] using wordTrace_append hprefix tailTrace_435210
  have hstable : (prefixWord ++ tailWord_435210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435210).length < 2 ^ (prefixWord ++ tailWord_435210).sum := by decide
  have hdescent : baseEnd_435210 < baseStart_435210 := by decide
  rcases family_descends (prefixWord ++ tailWord_435210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435269 : List Nat := [1, 3, 1, 1, 1, 3, 4, 4, 3]
def baseStart_435269 : Nat := 118140960795 + 435269 * 2 ^ 59
def prefixEnd_435269 : Nat := 4983230072969 + 3 ^ 40 * 435269 * 2
def baseEnd_435269 : Nat := 99334316000872329660329

theorem tailTrace_435269 : CollatzResearch.WordTrace tailWord_435269 prefixEnd_435269 99334316000872329660329 := by
  unfold tailWord_435269
  simp only [CollatzResearch.WordTrace]
  refine ⟨15875564660102225871956861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10583709773401483914637907 15875564660102225871956861)
  ·
    refine ⟨5953336747538334701983823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15875564660102225871956861 5953336747538334701983823)
    ·
      refine ⟨8930005121307502052975735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5953336747538334701983823 8930005121307502052975735)
      ·
        refine ⟨13395007681961253079463603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8930005121307502052975735 13395007681961253079463603)
        ·
          refine ⟨20092511522941879619195405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13395007681961253079463603 20092511522941879619195405)
          ·
            refine ⟨7534691821103204857198277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20092511522941879619195405 7534691821103204857198277)
            ·
              refine ⟨1412754716456850910724677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7534691821103204857198277 1412754716456850910724677)
              ·
                refine ⟨264891509335659545760877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1412754716456850910724677 264891509335659545760877)
                ·
                  refine ⟨99334316000872329660329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264891509335659545760877 99334316000872329660329)
                  ·
                    rfl

theorem cell21_435269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_435269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435269 prefixEnd_435269 := by exact prefixLift 435269
  have htrace : WordTrace (prefixWord ++ tailWord_435269) baseStart_435269 baseEnd_435269 := by
    simpa [prefixWord, tailWord_435269, baseEnd_435269] using wordTrace_append hprefix tailTrace_435269
  have hstable : (prefixWord ++ tailWord_435269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435269).length < 2 ^ (prefixWord ++ tailWord_435269).sum := by decide
  have hdescent : baseEnd_435269 < baseStart_435269 := by decide
  rcases family_descends (prefixWord ++ tailWord_435269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435328 : List Nat := [2, 1, 1, 2, 1, 3, 5, 1, 5]
def baseStart_435328 : Nat := 118140960795 + 435328 * 2 ^ 59
def prefixEnd_435328 : Nat := 4983230072969 + 3 ^ 40 * 435328 * 2
def baseEnd_435328 : Nat := 99347780604701338176875

theorem tailTrace_435328 : CollatzResearch.WordTrace tailWord_435328 prefixEnd_435328 99347780604701338176875 := by
  unfold tailWord_435328
  simp only [CollatzResearch.WordTrace]
  refine ⟨7938858283444239474177319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10585144377925652632236425 7938858283444239474177319)
  ·
    refine ⟨11908287425166359211265979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7938858283444239474177319 11908287425166359211265979)
    ·
      refine ⟨17862431137749538816898969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11908287425166359211265979 17862431137749538816898969)
      ·
        refine ⟨13396823353312154112674227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17862431137749538816898969 13396823353312154112674227)
        ·
          refine ⟨20095235029968231169011341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13396823353312154112674227 20095235029968231169011341)
          ·
            refine ⟨7535713136238086688379253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20095235029968231169011341 7535713136238086688379253)
            ·
              refine ⟨706473106522320627035555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7535713136238086688379253 706473106522320627035555)
              ·
                refine ⟨1059709659783480940553333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706473106522320627035555 1059709659783480940553333)
                ·
                  refine ⟨99347780604701338176875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1059709659783480940553333 99347780604701338176875)
                  ·
                    rfl

theorem cell21_435328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_435328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435328 prefixEnd_435328 := by exact prefixLift 435328
  have htrace : WordTrace (prefixWord ++ tailWord_435328) baseStart_435328 baseEnd_435328 := by
    simpa [prefixWord, tailWord_435328, baseEnd_435328] using wordTrace_append hprefix tailTrace_435328
  have hstable : (prefixWord ++ tailWord_435328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435328).length < 2 ^ (prefixWord ++ tailWord_435328).sum := by decide
  have hdescent : baseEnd_435328 < baseStart_435328 := by decide
  rcases family_descends (prefixWord ++ tailWord_435328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435373 : List Nat := [1, 5, 2, 1, 12]
def baseStart_435373 : Nat := 118140960795 + 435373 * 2 ^ 59
def prefixEnd_435373 : Nat := 4983230072969 + 3 ^ 40 * 435373 * 2
def baseEnd_435373 : Nat := 1226642595281373579343

theorem tailTrace_435373 : CollatzResearch.WordTrace tailWord_435373 prefixEnd_435373 1226642595281373579343 := by
  unfold tailWord_435373
  simp only [CollatzResearch.WordTrace]
  refine ⟨15879357851725451633742773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10586238567816967755828515 15879357851725451633742773)
  ·
    refine ⟨1488689798599261090663385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15879357851725451633742773 1488689798599261090663385)
    ·
      refine ⟨1116517348949445817997539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1488689798599261090663385 1116517348949445817997539)
      ·
        refine ⟨1674776023424168726996309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1116517348949445817997539 1674776023424168726996309)
        ·
          refine ⟨1226642595281373579343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1674776023424168726996309 1226642595281373579343)
          ·
            rfl

theorem cell21_435373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 12].length) (baseStart_435373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435373 prefixEnd_435373 := by exact prefixLift 435373
  have htrace : WordTrace (prefixWord ++ tailWord_435373) baseStart_435373 baseEnd_435373 := by
    simpa [prefixWord, tailWord_435373, baseEnd_435373] using wordTrace_append hprefix tailTrace_435373
  have hstable : (prefixWord ++ tailWord_435373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435373).length < 2 ^ (prefixWord ++ tailWord_435373).sum := by decide
  have hdescent : baseEnd_435373 < baseStart_435373 := by decide
  rcases family_descends (prefixWord ++ tailWord_435373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435390 : List Nat := [4, 2, 1, 1, 3, 1, 3, 6]
def baseStart_435390 : Nat := 118140960795 + 435390 * 2 ^ 59
def prefixEnd_435390 : Nat := 4983230072969 + 3 ^ 40 * 435390 * 2
def baseEnd_435390 : Nat := 33120643283134336047805

theorem tailTrace_435390 : CollatzResearch.WordTrace tailWord_435390 prefixEnd_435390 33120643283134336047805 := by
  unfold tailWord_435390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1984997236582982942138953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10586651928442575691407749 1984997236582982942138953)
  ·
    refine ⟨1488747927437237206604215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1984997236582982942138953 1488747927437237206604215)
    ·
      refine ⟨2233121891155855809906323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1488747927437237206604215 2233121891155855809906323)
      ·
        refine ⟨3349682836733783714859485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2233121891155855809906323 3349682836733783714859485)
        ·
          refine ⟨1256131063775168893072307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3349682836733783714859485 1256131063775168893072307)
          ·
            refine ⟨1884196595662753339608461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256131063775168893072307 1884196595662753339608461)
            ·
              refine ⟨706573723373532502353173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1884196595662753339608461 706573723373532502353173)
              ·
                refine ⟨33120643283134336047805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 706573723373532502353173 33120643283134336047805)
                ·
                  rfl

theorem cell21_435390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_435390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435390 prefixEnd_435390 := by exact prefixLift 435390
  have htrace : WordTrace (prefixWord ++ tailWord_435390) baseStart_435390 baseEnd_435390 := by
    simpa [prefixWord, tailWord_435390, baseEnd_435390] using wordTrace_append hprefix tailTrace_435390
  have hstable : (prefixWord ++ tailWord_435390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435390).length < 2 ^ (prefixWord ++ tailWord_435390).sum := by decide
  have hdescent : baseEnd_435390 < baseStart_435390 := by decide
  rcases family_descends (prefixWord ++ tailWord_435390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435418 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 6]
def baseStart_435418 : Nat := 118140960795 + 435418 * 2 ^ 59
def prefixEnd_435418 : Nat := 4983230072969 + 3 ^ 40 * 435418 * 2
def baseEnd_435418 : Nat := 99368319830881181676691

theorem tailTrace_435418 : CollatzResearch.WordTrace tailWord_435418 prefixEnd_435418 99368319830881181676691 := by
  unfold tailWord_435418
  simp only [CollatzResearch.WordTrace]
  refine ⟨3970249784140606079782727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10587332757708282879420605 3970249784140606079782727)
  ·
    refine ⟨5955374676210909119674091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3970249784140606079782727 5955374676210909119674091)
    ·
      refine ⟨8933062014316363679511137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5955374676210909119674091 8933062014316363679511137)
      ·
        refine ⟨6699796510737272759633353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8933062014316363679511137 6699796510737272759633353)
        ·
          refine ⟨5024847383052954569725015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6699796510737272759633353 5024847383052954569725015)
          ·
            refine ⟨7537271074579431854587523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5024847383052954569725015 7537271074579431854587523)
            ·
              refine ⟨11305906611869147781881285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7537271074579431854587523 11305906611869147781881285)
              ·
                refine ⟨2119857489725465209102741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11305906611869147781881285 2119857489725465209102741)
                ·
                  refine ⟨99368319830881181676691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2119857489725465209102741 99368319830881181676691)
                  ·
                    rfl

theorem cell21_435418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_435418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435418 prefixEnd_435418 := by exact prefixLift 435418
  have htrace : WordTrace (prefixWord ++ tailWord_435418) baseStart_435418 baseEnd_435418 := by
    simpa [prefixWord, tailWord_435418, baseEnd_435418] using wordTrace_append hprefix tailTrace_435418
  have hstable : (prefixWord ++ tailWord_435418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435418).length < 2 ^ (prefixWord ++ tailWord_435418).sum := by decide
  have hdescent : baseEnd_435418 < baseStart_435418 := by decide
  rcases family_descends (prefixWord ++ tailWord_435418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435435 : List Nat := [1, 1, 1, 1, 2, 6, 3, 2, 4]
def baseStart_435435 : Nat := 118140960795 + 435435 * 2 ^ 59
def prefixEnd_435435 : Nat := 4983230072969 + 3 ^ 40 * 435435 * 2
def baseEnd_435435 : Nat := 99372199462492929893323

theorem tailTrace_435435 : CollatzResearch.WordTrace tailWord_435435 prefixEnd_435435 99372199462492929893323 := by
  unfold tailWord_435435
  simp only [CollatzResearch.WordTrace]
  refine ⟨15881619177500836222499759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10587746118333890814999839 15881619177500836222499759)
  ·
    refine ⟨23822428766251254333749639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15881619177500836222499759 23822428766251254333749639)
    ·
      refine ⟨35733643149376881500624459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23822428766251254333749639 35733643149376881500624459)
      ·
        refine ⟨53600464724065322250936689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35733643149376881500624459 53600464724065322250936689)
        ·
          refine ⟨40200348543048991688202517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53600464724065322250936689 40200348543048991688202517)
          ·
            refine ⟨1884391337955421485384493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40200348543048991688202517 1884391337955421485384493)
            ·
              refine ⟨706646751733283057019185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1884391337955421485384493 706646751733283057019185)
              ·
                refine ⟨529985063799962292764389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 706646751733283057019185 529985063799962292764389)
                ·
                  refine ⟨99372199462492929893323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 529985063799962292764389 99372199462492929893323)
                  ·
                    rfl

theorem cell21_435435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 4].length) (baseStart_435435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435435 prefixEnd_435435 := by exact prefixLift 435435
  have htrace : WordTrace (prefixWord ++ tailWord_435435) baseStart_435435 baseEnd_435435 := by
    simpa [prefixWord, tailWord_435435, baseEnd_435435] using wordTrace_append hprefix tailTrace_435435
  have hstable : (prefixWord ++ tailWord_435435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435435).length < 2 ^ (prefixWord ++ tailWord_435435).sum := by decide
  have hdescent : baseEnd_435435 < baseStart_435435 := by decide
  rcases family_descends (prefixWord ++ tailWord_435435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435559 : List Nat := [1, 1, 5, 1, 5, 1, 1, 6]
def baseStart_435559 : Nat := 118140960795 + 435559 * 2 ^ 59
def prefixEnd_435559 : Nat := 4983230072969 + 3 ^ 40 * 435559 * 2
def baseEnd_435559 : Nat := 33133499317298756608801

theorem tailTrace_435559 : CollatzResearch.WordTrace tailWord_435559 prefixEnd_435559 33133499317298756608801 := by
  unfold tailWord_435559
  simp only [CollatzResearch.WordTrace]
  refine ⟨15886141829051605400013731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10590761219367736933342487 15886141829051605400013731)
  ·
    refine ⟨23829212743577408100020597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15886141829051605400013731 23829212743577408100020597)
    ·
      refine ⟨2233988694710382009376931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23829212743577408100020597 2233988694710382009376931)
      ·
        refine ⟨3350983042065573014065397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2233988694710382009376931 3350983042065573014065397)
        ·
          refine ⟨314154660193647470068631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3350983042065573014065397 314154660193647470068631)
          ·
            refine ⟨471231990290471205102947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314154660193647470068631 471231990290471205102947)
            ·
              refine ⟨706847985435706807654421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471231990290471205102947 706847985435706807654421)
              ·
                refine ⟨33133499317298756608801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 706847985435706807654421 33133499317298756608801)
                ·
                  rfl

theorem cell21_435559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 6].length) (baseStart_435559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435559 prefixEnd_435559 := by exact prefixLift 435559
  have htrace : WordTrace (prefixWord ++ tailWord_435559) baseStart_435559 baseEnd_435559 := by
    simpa [prefixWord, tailWord_435559, baseEnd_435559] using wordTrace_append hprefix tailTrace_435559
  have hstable : (prefixWord ++ tailWord_435559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435559).length < 2 ^ (prefixWord ++ tailWord_435559).sum := by decide
  have hdescent : baseEnd_435559 < baseStart_435559 := by decide
  rcases family_descends (prefixWord ++ tailWord_435559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435573 : List Nat := [1, 3, 4, 1, 3, 1, 1, 2, 5]
def baseStart_435573 : Nat := 118140960795 + 435573 * 2 ^ 59
def prefixEnd_435573 : Nat := 4983230072969 + 3 ^ 40 * 435573 * 2
def baseEnd_435573 : Nat := 99403692942635356593041

theorem tailTrace_435573 : CollatzResearch.WordTrace tailWord_435573 prefixEnd_435573 99403692942635356593041 := by
  unfold tailWord_435573
  simp only [CollatzResearch.WordTrace]
  refine ⟨15886652451000885791023373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10591101634000590527348915 15886652451000885791023373)
  ·
    refine ⟨5957494669125332171633765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15886652451000885791023373 5957494669125332171633765)
    ·
      refine ⟨1117030250460999782181331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5957494669125332171633765 1117030250460999782181331)
      ·
        refine ⟨1675545375691499673271997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1117030250460999782181331 1675545375691499673271997)
        ·
          refine ⟨628329515884312377476999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1675545375691499673271997 628329515884312377476999)
          ·
            refine ⟨942494273826468566215499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628329515884312377476999 942494273826468566215499)
            ·
              refine ⟨1413741410739702849323249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 942494273826468566215499 1413741410739702849323249)
              ·
                refine ⟨1060306058054777136992437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1413741410739702849323249 1060306058054777136992437)
                ·
                  refine ⟨99403692942635356593041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1060306058054777136992437 99403692942635356593041)
                  ·
                    rfl

theorem cell21_435573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_435573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435573 prefixEnd_435573 := by exact prefixLift 435573
  have htrace : WordTrace (prefixWord ++ tailWord_435573) baseStart_435573 baseEnd_435573 := by
    simpa [prefixWord, tailWord_435573, baseEnd_435573] using wordTrace_append hprefix tailTrace_435573
  have hstable : (prefixWord ++ tailWord_435573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435573).length < 2 ^ (prefixWord ++ tailWord_435573).sum := by decide
  have hdescent : baseEnd_435573 < baseStart_435573 := by decide
  rcases family_descends (prefixWord ++ tailWord_435573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435584 : List Nat := [2, 1, 1, 2, 1, 2, 1, 11]
def baseStart_435584 : Nat := 118140960795 + 435584 * 2 ^ 59
def prefixEnd_435584 : Nat := 4983230072969 + 3 ^ 40 * 435584 * 2
def baseEnd_435584 : Nat := 33135401097500593969895

theorem tailTrace_435584 : CollatzResearch.WordTrace tailWord_435584 prefixEnd_435584 33135401097500593969895 := by
  unfold tailWord_435584
  simp only [CollatzResearch.WordTrace]
  refine ⟨7943526826980517334836903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10591369102640689779782537 7943526826980517334836903)
  ·
    refine ⟨11915290240470776002255355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7943526826980517334836903 11915290240470776002255355)
    ·
      refine ⟨17872935360706164003383033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11915290240470776002255355 17872935360706164003383033)
      ·
        refine ⟨13404701520529623002537275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17872935360706164003383033 13404701520529623002537275)
        ·
          refine ⟨20107052280794434503805913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13404701520529623002537275 20107052280794434503805913)
          ·
            refine ⟨15080289210595825877854435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20107052280794434503805913 15080289210595825877854435)
            ·
              refine ⟨22620433815893738816781653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15080289210595825877854435 22620433815893738816781653)
              ·
                refine ⟨33135401097500593969895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 22620433815893738816781653 33135401097500593969895)
                ·
                  rfl

theorem cell21_435584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 11].length) (baseStart_435584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435584 prefixEnd_435584 := by exact prefixLift 435584
  have htrace : WordTrace (prefixWord ++ tailWord_435584) baseStart_435584 baseEnd_435584 := by
    simpa [prefixWord, tailWord_435584, baseEnd_435584] using wordTrace_append hprefix tailTrace_435584
  have hstable : (prefixWord ++ tailWord_435584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435584).length < 2 ^ (prefixWord ++ tailWord_435584).sum := by decide
  have hdescent : baseEnd_435584 < baseStart_435584 := by decide
  rcases family_descends (prefixWord ++ tailWord_435584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435604 : List Nat := [2, 4, 2, 1, 2, 1, 3, 2, 4]
def baseStart_435604 : Nat := 118140960795 + 435604 * 2 ^ 59
def prefixEnd_435604 : Nat := 4983230072969 + 3 ^ 40 * 435604 * 2
def baseEnd_435604 : Nat := 99410767564986191576311

theorem tailTrace_435604 : CollatzResearch.WordTrace tailWord_435604 prefixEnd_435604 99410767564986191576311 := by
  unfold tailWord_435604
  simp only [CollatzResearch.WordTrace]
  refine ⟨7943891556944289042700933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10591855409259052056934577 7943891556944289042700933)
  ·
    refine ⟨1489479666927054195506425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7943891556944289042700933 1489479666927054195506425)
    ·
      refine ⟨1117109750195290646629819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1489479666927054195506425 1117109750195290646629819)
      ·
        refine ⟨1675664625292935969944729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1117109750195290646629819 1675664625292935969944729)
        ·
          refine ⟨1256748468969701977458547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1675664625292935969944729 1256748468969701977458547)
          ·
            refine ⟨1885122703454552966187821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256748468969701977458547 1885122703454552966187821)
            ·
              refine ⟨706921013795457362320433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1885122703454552966187821 706921013795457362320433)
              ·
                refine ⟨530190760346593021740325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 706921013795457362320433 530190760346593021740325)
                ·
                  refine ⟨99410767564986191576311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 530190760346593021740325 99410767564986191576311)
                  ·
                    rfl

theorem cell21_435604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_435604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435604 prefixEnd_435604 := by exact prefixLift 435604
  have htrace : WordTrace (prefixWord ++ tailWord_435604) baseStart_435604 baseEnd_435604 := by
    simpa [prefixWord, tailWord_435604, baseEnd_435604] using wordTrace_append hprefix tailTrace_435604
  have hstable : (prefixWord ++ tailWord_435604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435604).length < 2 ^ (prefixWord ++ tailWord_435604).sum := by decide
  have hdescent : baseEnd_435604 < baseStart_435604 := by decide
  rcases family_descends (prefixWord ++ tailWord_435604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435677 : List Nat := [1, 4, 3, 1, 1, 2, 1, 8]
def baseStart_435677 : Nat := 118140960795 + 435677 * 2 ^ 59
def prefixEnd_435677 : Nat := 4983230072969 + 3 ^ 40 * 435677 * 2
def baseEnd_435677 : Nat := 33142475719851428953165

theorem tailTrace_435677 : CollatzResearch.WordTrace tailWord_435677 prefixEnd_435677 33142475719851428953165 := by
  unfold tailWord_435677
  simp only [CollatzResearch.WordTrace]
  refine ⟨15890445642624111552809285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10593630428416074368539523 15890445642624111552809285)
  ·
    refine ⟨2979458557992020916151741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15890445642624111552809285 2979458557992020916151741)
    ·
      refine ⟨1117296959247007843556903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2979458557992020916151741 1117296959247007843556903)
      ·
        refine ⟨1675945438870511765335355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1117296959247007843556903 1675945438870511765335355)
        ·
          refine ⟨2513918158305767648003033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675945438870511765335355 2513918158305767648003033)
          ·
            refine ⟨1885438618729325736002275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2513918158305767648003033 1885438618729325736002275)
            ·
              refine ⟨2828157928093988604003413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885438618729325736002275 2828157928093988604003413)
              ·
                refine ⟨33142475719851428953165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2828157928093988604003413 33142475719851428953165)
                ·
                  rfl

theorem cell21_435677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 8].length) (baseStart_435677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435677 prefixEnd_435677 := by exact prefixLift 435677
  have htrace : WordTrace (prefixWord ++ tailWord_435677) baseStart_435677 baseEnd_435677 := by
    simpa [prefixWord, tailWord_435677, baseEnd_435677] using wordTrace_append hprefix tailTrace_435677
  have hstable : (prefixWord ++ tailWord_435677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435677).length < 2 ^ (prefixWord ++ tailWord_435677).sum := by decide
  have hdescent : baseEnd_435677 < baseStart_435677 := by decide
  rcases family_descends (prefixWord ++ tailWord_435677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435773 : List Nat := [1, 4, 1, 3, 4, 1, 1, 2, 4]
def baseStart_435773 : Nat := 118140960795 + 435773 * 2 ^ 59
def prefixEnd_435773 : Nat := 4983230072969 + 3 ^ 40 * 435773 * 2
def baseEnd_435773 : Nat := 99449335667479453259299

theorem tailTrace_435773 : CollatzResearch.WordTrace tailWord_435773 prefixEnd_435773 99449335667479453259299 := by
  unfold tailWord_435773
  simp only [CollatzResearch.WordTrace]
  refine ⟨15893947050276319948303973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10595964700184213298869315 15893947050276319948303973)
  ·
    refine ⟨2980115071926809990306995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15893947050276319948303973 2980115071926809990306995)
    ·
      refine ⟨4470172607890214985460493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2980115071926809990306995 4470172607890214985460493)
      ·
        refine ⟨1676314727958830619547685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4470172607890214985460493 1676314727958830619547685)
        ·
          refine ⟨314309011492280741165191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1676314727958830619547685 314309011492280741165191)
          ·
            refine ⟨471463517238421111747787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314309011492280741165191 471463517238421111747787)
            ·
              refine ⟨707195275857631667621681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471463517238421111747787 707195275857631667621681)
              ·
                refine ⟨530396456893223750716261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 707195275857631667621681 530396456893223750716261)
                ·
                  refine ⟨99449335667479453259299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 530396456893223750716261 99449335667479453259299)
                  ·
                    rfl

theorem cell21_435773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_435773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435773 prefixEnd_435773 := by exact prefixLift 435773
  have htrace : WordTrace (prefixWord ++ tailWord_435773) baseStart_435773 baseEnd_435773 := by
    simpa [prefixWord, tailWord_435773, baseEnd_435773] using wordTrace_append hprefix tailTrace_435773
  have hstable : (prefixWord ++ tailWord_435773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435773).length < 2 ^ (prefixWord ++ tailWord_435773).sum := by decide
  have hdescent : baseEnd_435773 < baseStart_435773 := by decide
  rcases family_descends (prefixWord ++ tailWord_435773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435818 : List Nat := [3, 1, 3, 2, 1, 4, 1, 3, 3]
def baseStart_435818 : Nat := 118140960795 + 435818 * 2 ^ 59
def prefixEnd_435818 : Nat := 4983230072969 + 3 ^ 40 * 435818 * 2
def baseEnd_435818 : Nat := 99459605280569375009207

theorem tailTrace_435818 : CollatzResearch.WordTrace tailWord_435818 prefixEnd_435818 99459605280569375009207 := by
  unfold tailWord_435818
  simp only [CollatzResearch.WordTrace]
  refine ⟨3973897083778323158423027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10597058890075528422461405 3973897083778323158423027)
  ·
    refine ⟨5960845625667484737634541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3973897083778323158423027 5960845625667484737634541)
    ·
      refine ⟨2235317109625306776612953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5960845625667484737634541 2235317109625306776612953)
      ·
        refine ⟨1676487832218980082459715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2235317109625306776612953 1676487832218980082459715)
        ·
          refine ⟨2514731748328470123689573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1676487832218980082459715 2514731748328470123689573)
          ·
            refine ⟨471512202811588148191795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2514731748328470123689573 471512202811588148191795)
            ·
              refine ⟨707268304217382222287693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471512202811588148191795 707268304217382222287693)
              ·
                refine ⟨265225614081518333357885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 707268304217382222287693 265225614081518333357885)
                ·
                  refine ⟨99459605280569375009207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265225614081518333357885 99459605280569375009207)
                  ·
                    rfl

theorem cell21_435818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_435818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435818 prefixEnd_435818 := by exact prefixLift 435818
  have htrace : WordTrace (prefixWord ++ tailWord_435818) baseStart_435818 baseEnd_435818 := by
    simpa [prefixWord, tailWord_435818, baseEnd_435818] using wordTrace_append hprefix tailTrace_435818
  have hstable : (prefixWord ++ tailWord_435818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435818).length < 2 ^ (prefixWord ++ tailWord_435818).sum := by decide
  have hdescent : baseEnd_435818 < baseStart_435818 := by decide
  rcases family_descends (prefixWord ++ tailWord_435818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435829 : List Nat := [1, 3, 4, 2, 1, 1, 9]
def baseStart_435829 : Nat := 118140960795 + 435829 * 2 ^ 59
def prefixEnd_435829 : Nat := 4983230072969 + 3 ^ 40 * 435829 * 2
def baseEnd_435829 : Nat := 11051346181159533369539

theorem tailTrace_435829 : CollatzResearch.WordTrace tailWord_435829 prefixEnd_435829 11051346181159533369539 := by
  unfold tailWord_435829
  simp only [CollatzResearch.WordTrace]
  refine ⟨15895989538073441512342541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10597326358715627674895027 15895989538073441512342541)
  ·
    refine ⟨5960996076777540567128453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15895989538073441512342541 5960996076777540567128453)
    ·
      refine ⟨1117686764395788856336585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5960996076777540567128453 1117686764395788856336585)
      ·
        refine ⟨838265073296841642252439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1117686764395788856336585 838265073296841642252439)
        ·
          refine ⟨1257397609945262463378659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838265073296841642252439 1257397609945262463378659)
          ·
            refine ⟨1886096414917893695067989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257397609945262463378659 1886096414917893695067989)
            ·
              refine ⟨11051346181159533369539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1886096414917893695067989 11051346181159533369539)
              ·
                rfl

theorem cell21_435829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 9].length) (baseStart_435829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435829 prefixEnd_435829 := by exact prefixLift 435829
  have htrace : WordTrace (prefixWord ++ tailWord_435829) baseStart_435829 baseEnd_435829 := by
    simpa [prefixWord, tailWord_435829, baseEnd_435829] using wordTrace_append hprefix tailTrace_435829
  have hstable : (prefixWord ++ tailWord_435829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435829).length < 2 ^ (prefixWord ++ tailWord_435829).sum := by decide
  have hdescent : baseEnd_435829 < baseStart_435829 := by decide
  rcases family_descends (prefixWord ++ tailWord_435829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435857 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 8]
def baseStart_435857 : Nat := 118140960795 + 435857 * 2 ^ 59
def prefixEnd_435857 : Nat := 4983230072969 + 3 ^ 40 * 435857 * 2
def baseEnd_435857 : Nat := 99468505611913973859127

theorem tailTrace_435857 : CollatzResearch.WordTrace tailWord_435857 prefixEnd_435857 99468505611913973859127 := by
  unfold tailWord_435857
  simp only [CollatzResearch.WordTrace]
  refine ⟨15897010781972002294361825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10598007187981334862907883 15897010781972002294361825)
  ·
    refine ⟨11922758086479001720771369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15897010781972002294361825 11922758086479001720771369)
    ·
      refine ⟨8942068564859251290578527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11922758086479001720771369 8942068564859251290578527)
      ·
        refine ⟨13413102847288876935867791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8942068564859251290578527 13413102847288876935867791)
        ·
          refine ⟨20119654270933315403801687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13413102847288876935867791 20119654270933315403801687)
          ·
            refine ⟨30179481406399973105702531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20119654270933315403801687 30179481406399973105702531)
            ·
              refine ⟨45269222109599959658553797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30179481406399973105702531 45269222109599959658553797)
              ·
                refine ⟨8487979145549992435978837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45269222109599959658553797 8487979145549992435978837)
                ·
                  refine ⟨99468505611913973859127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8487979145549992435978837 99468505611913973859127)
                  ·
                    rfl

theorem cell21_435857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_435857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435857 prefixEnd_435857 := by exact prefixLift 435857
  have htrace : WordTrace (prefixWord ++ tailWord_435857) baseStart_435857 baseEnd_435857 := by
    simpa [prefixWord, tailWord_435857, baseEnd_435857] using wordTrace_append hprefix tailTrace_435857
  have hstable : (prefixWord ++ tailWord_435857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435857).length < 2 ^ (prefixWord ++ tailWord_435857).sum := by decide
  have hdescent : baseEnd_435857 < baseStart_435857 := by decide
  rcases family_descends (prefixWord ++ tailWord_435857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435922 : List Nat := [3, 2, 2, 2, 2, 2, 3, 5]
def baseStart_435922 : Nat := 118140960795 + 435922 * 2 ^ 59
def prefixEnd_435922 : Nat := 4983230072969 + 3 ^ 40 * 435922 * 2
def baseEnd_435922 : Nat := 33161113165829435091887

theorem tailTrace_435922 : CollatzResearch.WordTrace tailWord_435922 prefixEnd_435922 33161113165829435091887 := by
  unfold tailWord_435922
  simp only [CollatzResearch.WordTrace]
  refine ⟨3974845381684129598869505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10599587684491012263652013 3974845381684129598869505)
  ·
    refine ⟨2981134036263097199152129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3974845381684129598869505 2981134036263097199152129)
    ·
      refine ⟨2235850527197322899364097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2981134036263097199152129 2235850527197322899364097)
      ·
        refine ⟨1676887895397992174523073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2235850527197322899364097 1676887895397992174523073)
        ·
          refine ⟨1257665921548494130892305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1676887895397992174523073 1257665921548494130892305)
          ·
            refine ⟨943249441161370598169229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1257665921548494130892305 943249441161370598169229)
            ·
              refine ⟨353718540435513974313461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 943249441161370598169229 353718540435513974313461)
              ·
                refine ⟨33161113165829435091887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 353718540435513974313461 33161113165829435091887)
                ·
                  rfl

theorem cell21_435922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_435922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435922 prefixEnd_435922 := by exact prefixLift 435922
  have htrace : WordTrace (prefixWord ++ tailWord_435922) baseStart_435922 baseEnd_435922 := by
    simpa [prefixWord, tailWord_435922, baseEnd_435922] using wordTrace_append hprefix tailTrace_435922
  have hstable : (prefixWord ++ tailWord_435922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435922).length < 2 ^ (prefixWord ++ tailWord_435922).sum := by decide
  have hdescent : baseEnd_435922 < baseStart_435922 := by decide
  rcases family_descends (prefixWord ++ tailWord_435922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435936 : List Nat := [2, 1, 1, 3, 1, 2, 3, 5, 3]
def baseStart_435936 : Nat := 118140960795 + 435936 * 2 ^ 59
def prefixEnd_435936 : Nat := 4983230072969 + 3 ^ 40 * 435936 * 2
def baseEnd_435936 : Nat := 99486534488227392042299

theorem tailTrace_435936 : CollatzResearch.WordTrace tailWord_435936 prefixEnd_435936 99486534488227392042299 := by
  unfold tailWord_435936
  simp only [CollatzResearch.WordTrace]
  refine ⟨7949946074342899393243831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10599928099123865857658441 7949946074342899393243831)
  ·
    refine ⟨11924919111514349089865747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7949946074342899393243831 11924919111514349089865747)
    ·
      refine ⟨17887378667271523634798621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11924919111514349089865747 17887378667271523634798621)
      ·
        refine ⟨6707767000226821363049483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17887378667271523634798621 6707767000226821363049483)
        ·
          refine ⟨10061650500340232044574225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6707767000226821363049483 10061650500340232044574225)
          ·
            refine ⟨7546237875255174033430669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10061650500340232044574225 7546237875255174033430669)
            ·
              refine ⟨2829839203220690262536501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7546237875255174033430669 2829839203220690262536501)
              ·
                refine ⟨265297425301939712112797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2829839203220690262536501 265297425301939712112797)
                ·
                  refine ⟨99486534488227392042299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265297425301939712112797 99486534488227392042299)
                  ·
                    rfl

theorem cell21_435936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 3].length) (baseStart_435936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435936 prefixEnd_435936 := by exact prefixLift 435936
  have htrace : WordTrace (prefixWord ++ tailWord_435936) baseStart_435936 baseEnd_435936 := by
    simpa [prefixWord, tailWord_435936, baseEnd_435936] using wordTrace_append hprefix tailTrace_435936
  have hstable : (prefixWord ++ tailWord_435936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435936).length < 2 ^ (prefixWord ++ tailWord_435936).sum := by decide
  have hdescent : baseEnd_435936 < baseStart_435936 := by decide
  rcases family_descends (prefixWord ++ tailWord_435936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435950 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_435950 : Nat := 118140960795 + 435950 * 2 ^ 59
def prefixEnd_435950 : Nat := 4983230072969 + 3 ^ 40 * 435950 * 2
def baseEnd_435950 : Nat := 99489729478966478808937

theorem tailTrace_435950 : CollatzResearch.WordTrace tailWord_435950 prefixEnd_435950 99489729478966478808937 := by
  unfold tailWord_435950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1987550346329384897187163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10600268513756719451664869 1987550346329384897187163)
  ·
    refine ⟨2981325519494077345780745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1987550346329384897187163 2981325519494077345780745)
    ·
      refine ⟨2235994139620558009335559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2981325519494077345780745 2235994139620558009335559)
      ·
        refine ⟨3353991209430837014003339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2235994139620558009335559 3353991209430837014003339)
        ·
          refine ⟨5030986814146255521005009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3353991209430837014003339 5030986814146255521005009)
          ·
            refine ⟨3773240110609691640753757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5030986814146255521005009 3773240110609691640753757)
            ·
              refine ⟨1414965041478634365282659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3773240110609691640753757 1414965041478634365282659)
              ·
                refine ⟨2122447562217951547923989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1414965041478634365282659 2122447562217951547923989)
                ·
                  refine ⟨99489729478966478808937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2122447562217951547923989 99489729478966478808937)
                  ·
                    rfl

theorem cell21_435950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_435950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435950 prefixEnd_435950 := by exact prefixLift 435950
  have htrace : WordTrace (prefixWord ++ tailWord_435950) baseStart_435950 baseEnd_435950 := by
    simpa [prefixWord, tailWord_435950, baseEnd_435950] using wordTrace_append hprefix tailTrace_435950
  have hstable : (prefixWord ++ tailWord_435950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435950).length < 2 ^ (prefixWord ++ tailWord_435950).sum := by decide
  have hdescent : baseEnd_435950 < baseStart_435950 := by decide
  rcases family_descends (prefixWord ++ tailWord_435950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435964 : List Nat := [2, 2, 2, 1, 3, 1, 2, 8]
def baseStart_435964 : Nat := 118140960795 + 435964 * 2 ^ 59
def prefixEnd_435964 : Nat := 4983230072969 + 3 ^ 40 * 435964 * 2
def baseEnd_435964 : Nat := 33164308156568521858525

theorem tailTrace_435964 : CollatzResearch.WordTrace tailWord_435964 prefixEnd_435964 33164308156568521858525 := by
  unfold tailWord_435964
  simp only [CollatzResearch.WordTrace]
  refine ⟨7950456696292179784253473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10600608928389573045671297 7950456696292179784253473)
  ·
    refine ⟨5962842522219134838190105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7950456696292179784253473 5962842522219134838190105)
    ·
      refine ⟨4472131891664351128642579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5962842522219134838190105 4472131891664351128642579)
      ·
        refine ⟨6708197837496526692963869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4472131891664351128642579 6708197837496526692963869)
        ·
          refine ⟨2515574189061197509861451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6708197837496526692963869 2515574189061197509861451)
          ·
            refine ⟨3773361283591796264792177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2515574189061197509861451 3773361283591796264792177)
            ·
              refine ⟨2830020962693847198594133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3773361283591796264792177 2830020962693847198594133)
              ·
                refine ⟨33164308156568521858525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2830020962693847198594133 33164308156568521858525)
                ·
                  rfl

theorem cell21_435964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 8].length) (baseStart_435964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435964 prefixEnd_435964 := by exact prefixLift 435964
  have htrace : WordTrace (prefixWord ++ tailWord_435964) baseStart_435964 baseEnd_435964 := by
    simpa [prefixWord, tailWord_435964, baseEnd_435964] using wordTrace_append hprefix tailTrace_435964
  have hstable : (prefixWord ++ tailWord_435964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435964).length < 2 ^ (prefixWord ++ tailWord_435964).sum := by decide
  have hdescent : baseEnd_435964 < baseStart_435964 := by decide
  rcases family_descends (prefixWord ++ tailWord_435964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436012 : List Nat := [2, 2, 1, 1, 1, 7, 1, 1, 5]
def baseStart_436012 : Nat := 118140960795 + 436012 * 2 ^ 59
def prefixEnd_436012 : Nat := 4983230072969 + 3 ^ 40 * 436012 * 2
def baseEnd_436012 : Nat := 99503878723668148775477

theorem tailTrace_436012 : CollatzResearch.WordTrace tailWord_436012 prefixEnd_436012 99503878723668148775477 := by
  unfold tailWord_436012
  simp only [CollatzResearch.WordTrace]
  refine ⟨7951332048205231883127145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10601776064273642510836193 7951332048205231883127145)
  ·
    refine ⟨5963499036153923912345359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7951332048205231883127145 5963499036153923912345359)
    ·
      refine ⟨8945248554230885868518039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5963499036153923912345359 8945248554230885868518039)
      ·
        refine ⟨13417872831346328802777059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8945248554230885868518039 13417872831346328802777059)
        ·
          refine ⟨20126809247019493204165589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13417872831346328802777059 20126809247019493204165589)
          ·
            refine ⟨471722091727019371972631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 20126809247019493204165589 471722091727019371972631)
            ·
              refine ⟨707583137590529057958947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471722091727019371972631 707583137590529057958947)
              ·
                refine ⟨1061374706385793586938421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 707583137590529057958947 1061374706385793586938421)
                ·
                  refine ⟨99503878723668148775477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1061374706385793586938421 99503878723668148775477)
                  ·
                    rfl

theorem cell21_436012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_436012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436012 prefixEnd_436012 := by exact prefixLift 436012
  have htrace : WordTrace (prefixWord ++ tailWord_436012) baseStart_436012 baseEnd_436012 := by
    simpa [prefixWord, tailWord_436012, baseEnd_436012] using wordTrace_append hprefix tailTrace_436012
  have hstable : (prefixWord ++ tailWord_436012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436012).length < 2 ^ (prefixWord ++ tailWord_436012).sum := by decide
  have hdescent : baseEnd_436012 < baseStart_436012 := by decide
  rcases family_descends (prefixWord ++ tailWord_436012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436040 : List Nat := [2, 1, 3, 1, 1, 4, 2, 7]
def baseStart_436040 : Nat := 118140960795 + 436040 * 2 ^ 59
def prefixEnd_436040 : Nat := 4983230072969 + 3 ^ 40 * 436040 * 2
def baseEnd_436040 : Nat := 33170089568382107436251

theorem tailTrace_436040 : CollatzResearch.WordTrace tailWord_436040 prefixEnd_436040 33170089568382107436251 := by
  unfold tailWord_436040
  simp only [CollatzResearch.WordTrace]
  refine ⟨7951842670154512274136787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10602456893539349698849049 7951842670154512274136787)
  ·
    refine ⟨11927764005231768411205181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7951842670154512274136787 11927764005231768411205181)
    ·
      refine ⟨4472911501961913154201943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11927764005231768411205181 4472911501961913154201943)
      ·
        refine ⟨6709367252942869731302915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4472911501961913154201943 6709367252942869731302915)
        ·
          refine ⟨10064050879414304596954373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6709367252942869731302915 10064050879414304596954373)
          ·
            refine ⟨1887009539890182111928945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10064050879414304596954373 1887009539890182111928945)
            ·
              refine ⟨1415257154917636583946709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1887009539890182111928945 1415257154917636583946709)
              ·
                refine ⟨33170089568382107436251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1415257154917636583946709 33170089568382107436251)
                ·
                  rfl

theorem cell21_436040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 7].length) (baseStart_436040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436040 prefixEnd_436040 := by exact prefixLift 436040
  have htrace : WordTrace (prefixWord ++ tailWord_436040) baseStart_436040 baseEnd_436040 := by
    simpa [prefixWord, tailWord_436040, baseEnd_436040] using wordTrace_append hprefix tailTrace_436040
  have hstable : (prefixWord ++ tailWord_436040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436040).length < 2 ^ (prefixWord ++ tailWord_436040).sum := by decide
  have hdescent : baseEnd_436040 < baseStart_436040 := by decide
  rcases family_descends (prefixWord ++ tailWord_436040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436060 : List Nat := [2, 2, 4, 2, 2, 1, 2, 2, 4]
def baseStart_436060 : Nat := 118140960795 + 436060 * 2 ^ 59
def prefixEnd_436060 : Nat := 4983230072969 + 3 ^ 40 * 436060 * 2
def baseEnd_436060 : Nat := 99514832977630731975379

theorem tailTrace_436060 : CollatzResearch.WordTrace tailWord_436060 prefixEnd_436060 99514832977630731975379 := by
  unfold tailWord_436060
  simp only [CollatzResearch.WordTrace]
  refine ⟨7952207400118283982000817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10602943200157711976001089 7952207400118283982000817)
  ·
    refine ⟨5964155550088712986500613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7952207400118283982000817 5964155550088712986500613)
    ·
      refine ⟨1118279165641633684968865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5964155550088712986500613 1118279165641633684968865)
      ·
        refine ⟨838709374231225263726649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1118279165641633684968865 838709374231225263726649)
        ·
          refine ⟨629032030673418947794987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 838709374231225263726649 629032030673418947794987)
          ·
            refine ⟨943548046010128421692481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629032030673418947794987 943548046010128421692481)
            ·
              refine ⟨707661034507596316269361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 943548046010128421692481 707661034507596316269361)
              ·
                refine ⟨530745775880697237202021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 707661034507596316269361 530745775880697237202021)
                ·
                  refine ⟨99514832977630731975379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 530745775880697237202021 99514832977630731975379)
                  ·
                    rfl

theorem cell21_436060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_436060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436060 prefixEnd_436060 := by exact prefixLift 436060
  have htrace : WordTrace (prefixWord ++ tailWord_436060) baseStart_436060 baseEnd_436060 := by
    simpa [prefixWord, tailWord_436060, baseEnd_436060] using wordTrace_append hprefix tailTrace_436060
  have hstable : (prefixWord ++ tailWord_436060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436060).length < 2 ^ (prefixWord ++ tailWord_436060).sum := by decide
  have hdescent : baseEnd_436060 < baseStart_436060 := by decide
  rcases family_descends (prefixWord ++ tailWord_436060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436071 : List Nat := [1, 1, 5, 1, 2, 1, 2, 3, 5]
def baseStart_436071 : Nat := 118140960795 + 436071 * 2 ^ 59
def prefixEnd_436071 : Nat := 4983230072969 + 3 ^ 40 * 436071 * 2
def baseEnd_436071 : Nat := 99517343327497157292023

theorem tailTrace_436071 : CollatzResearch.WordTrace tailWord_436071 prefixEnd_436071 99517343327497157292023 := by
  unfold tailWord_436071
  simp only [CollatzResearch.WordTrace]
  refine ⟨15904816003196716842652067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10603210668797811228434711 15904816003196716842652067)
  ·
    refine ⟨23857224004795075263978101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15904816003196716842652067 23857224004795075263978101)
    ·
      refine ⟨2236614750449538305997947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23857224004795075263978101 2236614750449538305997947)
      ·
        refine ⟨3354922125674307458996921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2236614750449538305997947 3354922125674307458996921)
        ·
          refine ⟨2516191594255730594247691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3354922125674307458996921 2516191594255730594247691)
          ·
            refine ⟨3774287391383595891371537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516191594255730594247691 3774287391383595891371537)
            ·
              refine ⟨2830715543537696918528653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3774287391383595891371537 2830715543537696918528653)
              ·
                refine ⟨1061518328826636344448245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2830715543537696918528653 1061518328826636344448245)
                ·
                  refine ⟨99517343327497157292023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1061518328826636344448245 99517343327497157292023)
                  ·
                    rfl

theorem cell21_436071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 5].length) (baseStart_436071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436071 prefixEnd_436071 := by exact prefixLift 436071
  have htrace : WordTrace (prefixWord ++ tailWord_436071) baseStart_436071 baseEnd_436071 := by
    simpa [prefixWord, tailWord_436071, baseEnd_436071] using wordTrace_append hprefix tailTrace_436071
  have hstable : (prefixWord ++ tailWord_436071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436071).length < 2 ^ (prefixWord ++ tailWord_436071).sum := by decide
  have hdescent : baseEnd_436071 < baseStart_436071 := by decide
  rcases family_descends (prefixWord ++ tailWord_436071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436119 : List Nat := [1, 1, 3, 3, 1, 5, 1, 2, 4]
def baseStart_436119 : Nat := 118140960795 + 436119 * 2 ^ 59
def prefixEnd_436119 : Nat := 4983230072969 + 3 ^ 40 * 436119 * 2
def baseEnd_436119 : Nat := 99528297581459740491925

theorem tailTrace_436119 : CollatzResearch.WordTrace tailWord_436119 prefixEnd_436119 99528297581459740491925 := by
  unfold tailWord_436119
  simp only [CollatzResearch.WordTrace]
  refine ⟨15906566707022821040399411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10604377804681880693599607 15906566707022821040399411)
  ·
    refine ⟨23859850060534231560599117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15906566707022821040399411 23859850060534231560599117)
    ·
      refine ⟨8947443772700336835224669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23859850060534231560599117 8947443772700336835224669)
      ·
        refine ⟨3355291414762626313209251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8947443772700336835224669 3355291414762626313209251)
        ·
          refine ⟨5032937122143939469813877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3355291414762626313209251 5032937122143939469813877)
          ·
            refine ⟨471837855200994325295051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5032937122143939469813877 471837855200994325295051)
            ·
              refine ⟨707756782801491487942577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471837855200994325295051 707756782801491487942577)
              ·
                refine ⟨530817587101118615956933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 707756782801491487942577 530817587101118615956933)
                ·
                  refine ⟨99528297581459740491925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 530817587101118615956933 99528297581459740491925)
                  ·
                    rfl

theorem cell21_436119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 4].length) (baseStart_436119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436119 prefixEnd_436119 := by exact prefixLift 436119
  have htrace : WordTrace (prefixWord ++ tailWord_436119) baseStart_436119 baseEnd_436119 := by
    simpa [prefixWord, tailWord_436119, baseEnd_436119] using wordTrace_append hprefix tailTrace_436119
  have hstable : (prefixWord ++ tailWord_436119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436119).length < 2 ^ (prefixWord ++ tailWord_436119).sum := by decide
  have hdescent : baseEnd_436119 < baseStart_436119 := by decide
  rcases family_descends (prefixWord ++ tailWord_436119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436195 : List Nat := [1, 1, 1, 6, 1, 2, 4, 1, 4]
def baseStart_436195 : Nat := 118140960795 + 436195 * 2 ^ 59
def prefixEnd_436195 : Nat := 4983230072969 + 3 ^ 40 * 436195 * 2
def baseEnd_436195 : Nat := 99545641816900497225103

theorem tailTrace_436195 : CollatzResearch.WordTrace tailWord_436195 prefixEnd_436195 99545641816900497225103 := by
  unfold tailWord_436195
  simp only [CollatzResearch.WordTrace]
  refine ⟨15909338654747486020166039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10606225769831657346777359 15909338654747486020166039)
  ·
    refine ⟨23864007982121229030249059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15909338654747486020166039 23864007982121229030249059)
    ·
      refine ⟨35796011973181843545373589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23864007982121229030249059 35796011973181843545373589)
      ·
        refine ⟨1677938061242898916189387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35796011973181843545373589 1677938061242898916189387)
        ·
          refine ⟨2516907091864348374284081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1677938061242898916189387 2516907091864348374284081)
          ·
            refine ⟨1887680318898261280713061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2516907091864348374284081 1887680318898261280713061)
            ·
              refine ⟨353940059793423990133699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1887680318898261280713061 353940059793423990133699)
              ·
                refine ⟨530910089690135985200549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353940059793423990133699 530910089690135985200549)
                ·
                  refine ⟨99545641816900497225103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 530910089690135985200549 99545641816900497225103)
                  ·
                    rfl

theorem cell21_436195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 4].length) (baseStart_436195 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436195 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436195 prefixEnd_436195 := by exact prefixLift 436195
  have htrace : WordTrace (prefixWord ++ tailWord_436195) baseStart_436195 baseEnd_436195 := by
    simpa [prefixWord, tailWord_436195, baseEnd_436195] using wordTrace_append hprefix tailTrace_436195
  have hstable : (prefixWord ++ tailWord_436195).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436195).length < 2 ^ (prefixWord ++ tailWord_436195).sum := by decide
  have hdescent : baseEnd_436195 < baseStart_436195 := by decide
  rcases family_descends (prefixWord ++ tailWord_436195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436251 : List Nat := [1, 1, 1, 1, 1, 1, 3, 12]
def baseStart_436251 : Nat := 118140960795 + 436251 * 2 ^ 59
def prefixEnd_436251 : Nat := 4983230072969 + 3 ^ 40 * 436251 * 2
def baseEnd_436251 : Nat := 33186140593285614763885

theorem tailTrace_436251 : CollatzResearch.WordTrace tailWord_436251 prefixEnd_436251 33186140593285614763885 := by
  unfold tailWord_436251
  simp only [CollatzResearch.WordTrace]
  refine ⟨15911381142544607584204607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10607587428363071722803071 15911381142544607584204607)
  ·
    refine ⟨23867071713816911376306911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15911381142544607584204607 23867071713816911376306911)
    ·
      refine ⟨35800607570725367064460367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23867071713816911376306911 35800607570725367064460367)
      ·
        refine ⟨53700911356088050596690551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35800607570725367064460367 53700911356088050596690551)
        ·
          refine ⟨80551367034132075895035827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53700911356088050596690551 80551367034132075895035827)
          ·
            refine ⟨120827050551198113842553741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80551367034132075895035827 120827050551198113842553741)
            ·
              refine ⟨45310143956699292690957653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120827050551198113842553741 45310143956699292690957653)
              ·
                refine ⟨33186140593285614763885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 45310143956699292690957653 33186140593285614763885)
                ·
                  rfl

theorem cell21_436251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 12].length) (baseStart_436251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436251 prefixEnd_436251 := by exact prefixLift 436251
  have htrace : WordTrace (prefixWord ++ tailWord_436251) baseStart_436251 baseEnd_436251 := by
    simpa [prefixWord, tailWord_436251, baseEnd_436251] using wordTrace_append hprefix tailTrace_436251
  have hstable : (prefixWord ++ tailWord_436251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436251).length < 2 ^ (prefixWord ++ tailWord_436251).sum := by decide
  have hdescent : baseEnd_436251 < baseStart_436251 := by decide
  rcases family_descends (prefixWord ++ tailWord_436251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436282 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 9]
def baseStart_436282 : Nat := 118140960795 + 436282 * 2 ^ 59
def prefixEnd_436282 : Nat := 4983230072969 + 3 ^ 40 * 436282 * 2
def baseEnd_436282 : Nat := 99565496402207679274925

theorem tailTrace_436282 : CollatzResearch.WordTrace tailWord_436282 prefixEnd_436282 99565496402207679274925 := by
  unfold tailWord_436282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3978127951358074969645775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10608341203621533252388733 3978127951358074969645775)
  ·
    refine ⟨5967191927037112454468663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3978127951358074969645775 5967191927037112454468663)
    ·
      refine ⟨8950787890555668681702995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5967191927037112454468663 8950787890555668681702995)
      ·
        refine ⟨13426181835833503022554493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8950787890555668681702995 13426181835833503022554493)
        ·
          refine ⟨5034818188437563633457935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13426181835833503022554493 5034818188437563633457935)
          ·
            refine ⟨7552227282656345450186903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5034818188437563633457935 7552227282656345450186903)
            ·
              refine ⟨11328340923984518175280355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7552227282656345450186903 11328340923984518175280355)
              ·
                refine ⟨16992511385976777262920533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11328340923984518175280355 16992511385976777262920533)
                ·
                  refine ⟨99565496402207679274925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16992511385976777262920533 99565496402207679274925)
                  ·
                    rfl

theorem cell21_436282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_436282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436282 prefixEnd_436282 := by exact prefixLift 436282
  have htrace : WordTrace (prefixWord ++ tailWord_436282) baseStart_436282 baseEnd_436282 := by
    simpa [prefixWord, tailWord_436282, baseEnd_436282] using wordTrace_append hprefix tailTrace_436282
  have hstable : (prefixWord ++ tailWord_436282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436282).length < 2 ^ (prefixWord ++ tailWord_436282).sum := by decide
  have hdescent : baseEnd_436282 < baseStart_436282 := by decide
  rcases family_descends (prefixWord ++ tailWord_436282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436479 : List Nat := [1, 1, 2, 2, 1, 4, 2, 8]
def baseStart_436479 : Nat := 118140960795 + 436479 * 2 ^ 59
def prefixEnd_436479 : Nat := 4983230072969 + 3 ^ 40 * 436479 * 2
def baseEnd_436479 : Nat := 33203484828726371497063

theorem tailTrace_436479 : CollatzResearch.WordTrace tailWord_436479 prefixEnd_436479 33203484828726371497063 := by
  unfold tailWord_436479
  simp only [CollatzResearch.WordTrace]
  refine ⟨15919696985718602523504491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10613131323812401682336327 15919696985718602523504491)
  ·
    refine ⟨23879545478577903785256737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15919696985718602523504491 23879545478577903785256737)
    ·
      refine ⟨17909659108933427838942553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23879545478577903785256737 17909659108933427838942553)
      ·
        refine ⟨13432244331700070879206915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17909659108933427838942553 13432244331700070879206915)
        ·
          refine ⟨20148366497550106318810373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13432244331700070879206915 20148366497550106318810373)
          ·
            refine ⟨3777818718290644934776945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20148366497550106318810373 3777818718290644934776945)
            ·
              refine ⟨2833364038717983701082709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3777818718290644934776945 2833364038717983701082709)
              ·
                refine ⟨33203484828726371497063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2833364038717983701082709 33203484828726371497063)
                ·
                  rfl

theorem cell21_436479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 8].length) (baseStart_436479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436479 prefixEnd_436479 := by exact prefixLift 436479
  have htrace : WordTrace (prefixWord ++ tailWord_436479) baseStart_436479 baseEnd_436479 := by
    simpa [prefixWord, tailWord_436479, baseEnd_436479] using wordTrace_append hprefix tailTrace_436479
  have hstable : (prefixWord ++ tailWord_436479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436479).length < 2 ^ (prefixWord ++ tailWord_436479).sum := by decide
  have hdescent : baseEnd_436479 < baseStart_436479 := by decide
  rcases family_descends (prefixWord ++ tailWord_436479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436519 : List Nat := [1, 1, 8, 1, 2, 1, 1, 1, 5]
def baseStart_436519 : Nat := 118140960795 + 436519 * 2 ^ 59
def prefixEnd_436519 : Nat := 4983230072969 + 3 ^ 40 * 436519 * 2
def baseEnd_436519 : Nat := 99619583031147933824441

theorem tailTrace_436519 : CollatzResearch.WordTrace tailWord_436519 prefixEnd_436519 99619583031147933824441 := by
  unfold tailWord_436519
  simp only [CollatzResearch.WordTrace]
  refine ⟨15921155905573689354960611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10614103937049126236640407 15921155905573689354960611)
  ·
    refine ⟨23881733858360534032440917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15921155905573689354960611 23881733858360534032440917)
    ·
      refine ⟨279864068652662508192667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 23881733858360534032440917 279864068652662508192667)
      ·
        refine ⟨419796102978993762289001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279864068652662508192667 419796102978993762289001)
        ·
          refine ⟨314847077234245321716751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419796102978993762289001 314847077234245321716751)
          ·
            refine ⟨472270615851367982575127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314847077234245321716751 472270615851367982575127)
            ·
              refine ⟨708405923777051973862691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472270615851367982575127 708405923777051973862691)
              ·
                refine ⟨1062608885665577960794037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708405923777051973862691 1062608885665577960794037)
                ·
                  refine ⟨99619583031147933824441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1062608885665577960794037 99619583031147933824441)
                  ·
                    rfl

theorem cell21_436519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 5].length) (baseStart_436519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436519 prefixEnd_436519 := by exact prefixLift 436519
  have htrace : WordTrace (prefixWord ++ tailWord_436519) baseStart_436519 baseEnd_436519 := by
    simpa [prefixWord, tailWord_436519, baseEnd_436519] using wordTrace_append hprefix tailTrace_436519
  have hstable : (prefixWord ++ tailWord_436519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436519).length < 2 ^ (prefixWord ++ tailWord_436519).sum := by decide
  have hdescent : baseEnd_436519 < baseStart_436519 := by decide
  rcases family_descends (prefixWord ++ tailWord_436519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436527 : List Nat := [1, 1, 2, 1, 2, 1, 4, 6, 3]
def baseStart_436527 : Nat := 118140960795 + 436527 * 2 ^ 59
def prefixEnd_436527 : Nat := 4983230072969 + 3 ^ 40 * 436527 * 2
def baseEnd_436527 : Nat := 99621408740141697691091

theorem tailTrace_436527 : CollatzResearch.WordTrace tailWord_436527 prefixEnd_436527 99621408740141697691091 := by
  unfold tailWord_436527
  simp only [CollatzResearch.WordTrace]
  refine ⟨15921447689544706721251835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10614298459696471147501223 15921447689544706721251835)
  ·
    refine ⟨23882171534317060081877753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15921447689544706721251835 23882171534317060081877753)
    ·
      refine ⟨17911628650737795061408315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23882171534317060081877753 17911628650737795061408315)
      ·
        refine ⟨26867442976106692592112473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17911628650737795061408315 26867442976106692592112473)
        ·
          refine ⟨20150582232080019444084355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26867442976106692592112473 20150582232080019444084355)
          ·
            refine ⟨30225873348120029166126533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20150582232080019444084355 30225873348120029166126533)
            ·
              refine ⟨5667351252772505468648725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30225873348120029166126533 5667351252772505468648725)
              ·
                refine ⟨265657089973711193842909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5667351252772505468648725 265657089973711193842909)
                ·
                  refine ⟨99621408740141697691091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265657089973711193842909 99621408740141697691091)
                  ·
                    rfl

theorem cell21_436527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 3].length) (baseStart_436527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436527 prefixEnd_436527 := by exact prefixLift 436527
  have htrace : WordTrace (prefixWord ++ tailWord_436527) baseStart_436527 baseEnd_436527 := by
    simpa [prefixWord, tailWord_436527, baseEnd_436527] using wordTrace_append hprefix tailTrace_436527
  have hstable : (prefixWord ++ tailWord_436527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436527).length < 2 ^ (prefixWord ++ tailWord_436527).sum := by decide
  have hdescent : baseEnd_436527 < baseStart_436527 := by decide
  rcases family_descends (prefixWord ++ tailWord_436527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436572 : List Nat := [2, 2, 4, 3, 10]
def baseStart_436572 : Nat := 118140960795 + 436572 * 2 ^ 59
def prefixEnd_436572 : Nat := 4983230072969 + 3 ^ 40 * 436572 * 2
def baseEnd_436572 : Nat := 1230020720410266906679

theorem tailTrace_436572 : CollatzResearch.WordTrace tailWord_436572 prefixEnd_436572 1230020720410266906679 := by
  unfold tailWord_436572
  simp only [CollatzResearch.WordTrace]
  refine ⟨7961544487190839703319985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10615392649587786271093313 7961544487190839703319985)
  ·
    refine ⟨5971158365393129777489989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7961544487190839703319985 5971158365393129777489989)
    ·
      refine ⟨1119592193511211833279373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5971158365393129777489989 1119592193511211833279373)
      ·
        refine ⟨419847072566704437479765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1119592193511211833279373 419847072566704437479765)
        ·
          refine ⟨1230020720410266906679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 419847072566704437479765 1230020720410266906679)
          ·
            rfl

theorem cell21_436572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 10].length) (baseStart_436572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436572 prefixEnd_436572 := by exact prefixLift 436572
  have htrace : WordTrace (prefixWord ++ tailWord_436572) baseStart_436572 baseEnd_436572 := by
    simpa [prefixWord, tailWord_436572, baseEnd_436572] using wordTrace_append hprefix tailTrace_436572
  have hstable : (prefixWord ++ tailWord_436572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436572).length < 2 ^ (prefixWord ++ tailWord_436572).sum := by decide
  have hdescent : baseEnd_436572 < baseStart_436572 := by decide
  rcases family_descends (prefixWord ++ tailWord_436572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436578 : List Nat := [3, 3, 2, 1, 1, 4, 2, 2, 3]
def baseStart_436578 : Nat := 118140960795 + 436578 * 2 ^ 59
def prefixEnd_436578 : Nat := 4983230072969 + 3 ^ 40 * 436578 * 2
def baseEnd_436578 : Nat := 99633047634976942340987

theorem tailTrace_436578 : CollatzResearch.WordTrace tailWord_436578 prefixEnd_436578 99633047634976942340987 := by
  unfold tailWord_436578
  simp only [CollatzResearch.WordTrace]
  refine ⟨3980826953089985607839597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10615538541573294954238925 3980826953089985607839597)
  ·
    refine ⟨1492810107408744602939849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3980826953089985607839597 1492810107408744602939849)
    ·
      refine ⟨1119607580556558452204887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1492810107408744602939849 1119607580556558452204887)
      ·
        refine ⟨1679411370834837678307331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119607580556558452204887 1679411370834837678307331)
        ·
          refine ⟨2519117056252256517460997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1679411370834837678307331 2519117056252256517460997)
          ·
            refine ⟨472334448047298097023937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2519117056252256517460997 472334448047298097023937)
            ·
              refine ⟨354250836035473572767953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472334448047298097023937 354250836035473572767953)
              ·
                refine ⟨265688127026605179575965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354250836035473572767953 265688127026605179575965)
                ·
                  refine ⟨99633047634976942340987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265688127026605179575965 99633047634976942340987)
                  ·
                    rfl

theorem cell21_436578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_436578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436578 prefixEnd_436578 := by exact prefixLift 436578
  have htrace : WordTrace (prefixWord ++ tailWord_436578) baseStart_436578 baseEnd_436578 := by
    simpa [prefixWord, tailWord_436578, baseEnd_436578] using wordTrace_append hprefix tailTrace_436578
  have hstable : (prefixWord ++ tailWord_436578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436578).length < 2 ^ (prefixWord ++ tailWord_436578).sum := by decide
  have hdescent : baseEnd_436578 < baseStart_436578 := by decide
  rcases family_descends (prefixWord ++ tailWord_436578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436620 : List Nat := [2, 2, 1, 2, 1, 5, 2, 3, 3]
def baseStart_436620 : Nat := 118140960795 + 436620 * 2 ^ 59
def prefixEnd_436620 : Nat := 4983230072969 + 3 ^ 40 * 436620 * 2
def baseEnd_436620 : Nat := 99642632607194202640901

theorem tailTrace_436620 : CollatzResearch.WordTrace tailWord_436620 prefixEnd_436620 99642632607194202640901 := by
  unfold tailWord_436620
  simp only [CollatzResearch.WordTrace]
  refine ⟨7962419839103891802193657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10616559785471855736258209 7962419839103891802193657)
  ·
    refine ⟨5971814879327918851645243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7962419839103891802193657 5971814879327918851645243)
    ·
      refine ⟨8957722318991878277467865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5971814879327918851645243 8957722318991878277467865)
      ·
        refine ⟨6718291739243908708100899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8957722318991878277467865 6718291739243908708100899)
        ·
          refine ⟨10077437608865863062151349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6718291739243908708100899 10077437608865863062151349)
          ·
            refine ⟨944759775831174662076689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10077437608865863062151349 944759775831174662076689)
            ·
              refine ⟨708569831873380996557517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 944759775831174662076689 708569831873380996557517)
              ·
                refine ⟨265713686952517873709069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 708569831873380996557517 265713686952517873709069)
                ·
                  refine ⟨99642632607194202640901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265713686952517873709069 99642632607194202640901)
                  ·
                    rfl

theorem cell21_436620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_436620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436620 prefixEnd_436620 := by exact prefixLift 436620
  have htrace : WordTrace (prefixWord ++ tailWord_436620) baseStart_436620 baseEnd_436620 := by
    simpa [prefixWord, tailWord_436620, baseEnd_436620] using wordTrace_append hprefix tailTrace_436620
  have hstable : (prefixWord ++ tailWord_436620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436620).length < 2 ^ (prefixWord ++ tailWord_436620).sum := by decide
  have hdescent : baseEnd_436620 < baseStart_436620 := by decide
  rcases family_descends (prefixWord ++ tailWord_436620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436634 : List Nat := [3, 1, 1, 4, 1, 2, 3, 2, 4]
def baseStart_436634 : Nat := 118140960795 + 436634 * 2 ^ 59
def prefixEnd_436634 : Nat := 4983230072969 + 3 ^ 40 * 436634 * 2
def baseEnd_436634 : Nat := 99645827597933289407539

theorem tailTrace_436634 : CollatzResearch.WordTrace tailWord_436634 prefixEnd_436634 99645827597933289407539 := by
  unfold tailWord_436634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3981337575039265998849239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10616900200104709330264637 3981337575039265998849239)
  ·
    refine ⟨5972006362558898998273859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3981337575039265998849239 5972006362558898998273859)
    ·
      refine ⟨8958009543838348497410789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5972006362558898998273859 8958009543838348497410789)
      ·
        refine ⟨1679626789469690343264523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8958009543838348497410789 1679626789469690343264523)
        ·
          refine ⟨2519440184204535514896785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1679626789469690343264523 2519440184204535514896785)
          ·
            refine ⟨1889580138153401636172589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2519440184204535514896785 1889580138153401636172589)
            ·
              refine ⟨708592551807525613564721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1889580138153401636172589 708592551807525613564721)
              ·
                refine ⟨531444413855644210173541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708592551807525613564721 531444413855644210173541)
                ·
                  refine ⟨99645827597933289407539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 531444413855644210173541 99645827597933289407539)
                  ·
                    rfl

theorem cell21_436634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_436634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436634 prefixEnd_436634 := by exact prefixLift 436634
  have htrace : WordTrace (prefixWord ++ tailWord_436634) baseStart_436634 baseEnd_436634 := by
    simpa [prefixWord, tailWord_436634, baseEnd_436634] using wordTrace_append hprefix tailTrace_436634
  have hstable : (prefixWord ++ tailWord_436634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436634).length < 2 ^ (prefixWord ++ tailWord_436634).sum := by decide
  have hdescent : baseEnd_436634 < baseStart_436634 := by decide
  rcases family_descends (prefixWord ++ tailWord_436634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436665 : List Nat := [1, 2, 1, 4, 3, 3, 2, 5]
def baseStart_436665 : Nat := 118140960795 + 436665 * 2 ^ 59
def prefixEnd_436665 : Nat := 4983230072969 + 3 ^ 40 * 436665 * 2
def baseEnd_436665 : Nat := 33217634073428041463603

theorem tailTrace_436665 : CollatzResearch.WordTrace tailWord_436665 prefixEnd_436665 33217634073428041463603 := by
  unfold tailWord_436665
  simp only [CollatzResearch.WordTrace]
  refine ⟨15926480963044756289775449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10617653975363170859850299 15926480963044756289775449)
  ·
    refine ⟨11944860722283567217331587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15926480963044756289775449 11944860722283567217331587)
    ·
      refine ⟨17917291083425350825997381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11944860722283567217331587 17917291083425350825997381)
      ·
        refine ⟨3359492078142253279874509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17917291083425350825997381 3359492078142253279874509)
        ·
          refine ⟨1259809529303344979952941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3359492078142253279874509 1259809529303344979952941)
          ·
            refine ⟨472428573488754367482353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1259809529303344979952941 472428573488754367482353)
            ·
              refine ⟨354321430116565775611765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472428573488754367482353 354321430116565775611765)
              ·
                refine ⟨33217634073428041463603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 354321430116565775611765 33217634073428041463603)
                ·
                  rfl

theorem cell21_436665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 5].length) (baseStart_436665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436665 prefixEnd_436665 := by exact prefixLift 436665
  have htrace : WordTrace (prefixWord ++ tailWord_436665) baseStart_436665 baseEnd_436665 := by
    simpa [prefixWord, tailWord_436665, baseEnd_436665] using wordTrace_append hprefix tailTrace_436665
  have hstable : (prefixWord ++ tailWord_436665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436665).length < 2 ^ (prefixWord ++ tailWord_436665).sum := by decide
  have hdescent : baseEnd_436665 < baseStart_436665 := by decide
  rcases family_descends (prefixWord ++ tailWord_436665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436693 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 6]
def baseStart_436693 : Nat := 118140960795 + 436693 * 2 ^ 59
def prefixEnd_436693 : Nat := 4983230072969 + 3 ^ 40 * 436693 * 2
def baseEnd_436693 : Nat := 99659292201762297924085

theorem tailTrace_436693 : CollatzResearch.WordTrace tailWord_436693 prefixEnd_436693 99659292201762297924085 := by
  unfold tailWord_436693
  simp only [CollatzResearch.WordTrace]
  refine ⟨15927502206943317071794733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10618334804628878047863155 15927502206943317071794733)
  ·
    refine ⟨5972813327603743901923025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15927502206943317071794733 5972813327603743901923025)
    ·
      refine ⟨4479609995702807926442269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5972813327603743901923025 4479609995702807926442269)
      ·
        refine ⟨1679853748388552972415851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4479609995702807926442269 1679853748388552972415851)
        ·
          refine ⟨2519780622582829458623777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1679853748388552972415851 2519780622582829458623777)
          ·
            refine ⟨1889835466937122093967833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2519780622582829458623777 1889835466937122093967833)
            ·
              refine ⟨1417376600202841570475875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1889835466937122093967833 1417376600202841570475875)
              ·
                refine ⟨2126064900304262355713813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1417376600202841570475875 2126064900304262355713813)
                ·
                  refine ⟨99659292201762297924085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2126064900304262355713813 99659292201762297924085)
                  ·
                    rfl

theorem cell21_436693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_436693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436693 prefixEnd_436693 := by exact prefixLift 436693
  have htrace : WordTrace (prefixWord ++ tailWord_436693) baseStart_436693 baseEnd_436693 := by
    simpa [prefixWord, tailWord_436693, baseEnd_436693] using wordTrace_append hprefix tailTrace_436693
  have hstable : (prefixWord ++ tailWord_436693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436693).length < 2 ^ (prefixWord ++ tailWord_436693).sum := by decide
  have hdescent : baseEnd_436693 < baseStart_436693 := by decide
  rcases family_descends (prefixWord ++ tailWord_436693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436755 : List Nat := [1, 1, 1, 2, 1, 5, 3, 4, 3]
def baseStart_436755 : Nat := 118140960795 + 436755 * 2 ^ 59
def prefixEnd_436755 : Nat := 4983230072969 + 3 ^ 40 * 436755 * 2
def baseEnd_436755 : Nat := 99673441446463967890625

theorem tailTrace_436755 : CollatzResearch.WordTrace tailWord_436755 prefixEnd_436755 99673441446463967890625 := by
  unfold tailWord_436755
  simp only [CollatzResearch.WordTrace]
  refine ⟨15929763532718701660551719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10619842355145801107034479 15929763532718701660551719)
  ·
    refine ⟨23894645299078052490827579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15929763532718701660551719 23894645299078052490827579)
    ·
      refine ⟨35841967948617078736241369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23894645299078052490827579 35841967948617078736241369)
      ·
        refine ⟨26881475961462809052181027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35841967948617078736241369 26881475961462809052181027)
        ·
          refine ⟨40322213942194213578271541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26881475961462809052181027 40322213942194213578271541)
          ·
            refine ⟨3780207557080707522962957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40322213942194213578271541 3780207557080707522962957)
            ·
              refine ⟨1417577833905265321111109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3780207557080707522962957 1417577833905265321111109)
              ·
                refine ⟨265795843857237247708333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1417577833905265321111109 265795843857237247708333)
                ·
                  refine ⟨99673441446463967890625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265795843857237247708333 99673441446463967890625)
                  ·
                    rfl

theorem cell21_436755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 3].length) (baseStart_436755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436755 prefixEnd_436755 := by exact prefixLift 436755
  have htrace : WordTrace (prefixWord ++ tailWord_436755) baseStart_436755 baseEnd_436755 := by
    simpa [prefixWord, tailWord_436755, baseEnd_436755] using wordTrace_append hprefix tailTrace_436755
  have hstable : (prefixWord ++ tailWord_436755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436755).length < 2 ^ (prefixWord ++ tailWord_436755).sum := by decide
  have hdescent : baseEnd_436755 < baseStart_436755 := by decide
  rcases family_descends (prefixWord ++ tailWord_436755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436769 : List Nat := [1, 2, 3, 2, 2, 1, 1, 5, 4]
def baseStart_436769 : Nat := 118140960795 + 436769 * 2 ^ 59
def prefixEnd_436769 : Nat := 4983230072969 + 3 ^ 40 * 436769 * 2
def baseEnd_436769 : Nat := 99676636437203054657263

theorem tailTrace_436769 : CollatzResearch.WordTrace tailWord_436769 prefixEnd_436769 99676636437203054657263 := by
  unfold tailWord_436769
  simp only [CollatzResearch.WordTrace]
  refine ⟨15930274154667982051561361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10620182769778654701040907 15930274154667982051561361)
  ·
    refine ⟨11947705616000986538671021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15930274154667982051561361 11947705616000986538671021)
    ·
      refine ⟨4480389606000369952001633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11947705616000986538671021 4480389606000369952001633)
      ·
        refine ⟨3360292204500277464001225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4480389606000369952001633 3360292204500277464001225)
        ·
          refine ⟨2520219153375208098000919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3360292204500277464001225 2520219153375208098000919)
          ·
            refine ⟨3780328730062812147001379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2520219153375208098000919 3780328730062812147001379)
            ·
              refine ⟨5670493095094218220502069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3780328730062812147001379 5670493095094218220502069)
              ·
                refine ⟨531608727665082958172069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5670493095094218220502069 531608727665082958172069)
                ·
                  refine ⟨99676636437203054657263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 531608727665082958172069 99676636437203054657263)
                  ·
                    rfl

theorem cell21_436769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_436769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436769 prefixEnd_436769 := by exact prefixLift 436769
  have htrace : WordTrace (prefixWord ++ tailWord_436769) baseStart_436769 baseEnd_436769 := by
    simpa [prefixWord, tailWord_436769, baseEnd_436769] using wordTrace_append hprefix tailTrace_436769
  have hstable : (prefixWord ++ tailWord_436769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436769).length < 2 ^ (prefixWord ++ tailWord_436769).sum := by decide
  have hdescent : baseEnd_436769 < baseStart_436769 := by decide
  rcases family_descends (prefixWord ++ tailWord_436769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436772 : List Nat := [2, 3, 1, 5, 1, 1, 1, 2, 5]
def baseStart_436772 : Nat := 118140960795 + 436772 * 2 ^ 59
def prefixEnd_436772 : Nat := 4983230072969 + 3 ^ 40 * 436772 * 2
def baseEnd_436772 : Nat := 99677321078075716107257

theorem tailTrace_436772 : CollatzResearch.WordTrace tailWord_436772 prefixEnd_436772 99677321078075716107257 := by
  unfold tailWord_436772
  simp only [CollatzResearch.WordTrace]
  refine ⟨7965191786828556781960285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10620255715771409042613713 7965191786828556781960285)
  ·
    refine ⟨2986946920060708793235107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7965191786828556781960285 2986946920060708793235107)
    ·
      refine ⟨4480420380091063189852661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2986946920060708793235107 4480420380091063189852661)
      ·
        refine ⟨420039410633537174048687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4480420380091063189852661 420039410633537174048687)
        ·
          refine ⟨630059115950305761073031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420039410633537174048687 630059115950305761073031)
          ·
            refine ⟨945088673925458641609547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630059115950305761073031 945088673925458641609547)
            ·
              refine ⟨1417633010888187962414321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945088673925458641609547 1417633010888187962414321)
              ·
                refine ⟨1063224758166140971810741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1417633010888187962414321 1063224758166140971810741)
                ·
                  refine ⟨99677321078075716107257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1063224758166140971810741 99677321078075716107257)
                  ·
                    rfl

theorem cell21_436772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_436772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436772 prefixEnd_436772 := by exact prefixLift 436772
  have htrace : WordTrace (prefixWord ++ tailWord_436772) baseStart_436772 baseEnd_436772 := by
    simpa [prefixWord, tailWord_436772, baseEnd_436772] using wordTrace_append hprefix tailTrace_436772
  have hstable : (prefixWord ++ tailWord_436772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436772).length < 2 ^ (prefixWord ++ tailWord_436772).sum := by decide
  have hdescent : baseEnd_436772 < baseStart_436772 := by decide
  rcases family_descends (prefixWord ++ tailWord_436772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436814 : List Nat := [4, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_436814 : Nat := 118140960795 + 436814 * 2 ^ 59
def prefixEnd_436814 : Nat := 4983230072969 + 3 ^ 40 * 436814 * 2
def baseEnd_436814 : Nat := 99686906050292976407171

theorem tailTrace_436814 : CollatzResearch.WordTrace tailWord_436814 prefixEnd_436814 99686906050292976407171 := by
  unfold tailWord_436814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1991489429938119342118687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10621276959669969824632997 1991489429938119342118687)
  ·
    refine ⟨2987234144907179013178031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1991489429938119342118687 2987234144907179013178031)
    ·
      refine ⟨4480851217360768519767047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2987234144907179013178031 4480851217360768519767047)
      ·
        refine ⟨6721276826041152779650571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4480851217360768519767047 6721276826041152779650571)
        ·
          refine ⟨10081915239061729169475857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6721276826041152779650571 10081915239061729169475857)
          ·
            refine ⟨7561436429296296877106893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10081915239061729169475857 7561436429296296877106893)
            ·
              refine ⟨2835538660986111328915085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7561436429296296877106893 2835538660986111328915085)
              ·
                refine ⟨1063326997869791748343157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2835538660986111328915085 1063326997869791748343157)
                ·
                  refine ⟨99686906050292976407171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1063326997869791748343157 99686906050292976407171)
                  ·
                    rfl

theorem cell21_436814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_436814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436814 prefixEnd_436814 := by exact prefixLift 436814
  have htrace : WordTrace (prefixWord ++ tailWord_436814) baseStart_436814 baseEnd_436814 := by
    simpa [prefixWord, tailWord_436814, baseEnd_436814] using wordTrace_append hprefix tailTrace_436814
  have hstable : (prefixWord ++ tailWord_436814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436814).length < 2 ^ (prefixWord ++ tailWord_436814).sum := by decide
  have hdescent : baseEnd_436814 < baseStart_436814 := by decide
  rcases family_descends (prefixWord ++ tailWord_436814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436845 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 6]
def baseStart_436845 : Nat := 118140960795 + 436845 * 2 ^ 59
def prefixEnd_436845 : Nat := 4983230072969 + 3 ^ 40 * 436845 * 2
def baseEnd_436845 : Nat := 99693980672643811390441

theorem tailTrace_436845 : CollatzResearch.WordTrace tailWord_436845 prefixEnd_436845 99693980672643811390441 := by
  unfold tailWord_436845
  simp only [CollatzResearch.WordTrace]
  refine ⟨15933046102392647031327989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10622030734928431354218659 15933046102392647031327989)
  ·
    refine ⟨1493723072099310659186999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15933046102392647031327989 1493723072099310659186999)
    ·
      refine ⟨2240584608148965988780499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1493723072099310659186999 2240584608148965988780499)
      ·
        refine ⟨3360876912223448983170749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2240584608148965988780499 3360876912223448983170749)
        ·
          refine ⟨1260328842083793368689031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3360876912223448983170749 1260328842083793368689031)
          ·
            refine ⟨1890493263125690053033547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260328842083793368689031 1890493263125690053033547)
            ·
              refine ⟨2835739894688535079550321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890493263125690053033547 2835739894688535079550321)
              ·
                refine ⟨2126804921016401309662741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2835739894688535079550321 2126804921016401309662741)
                ·
                  refine ⟨99693980672643811390441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2126804921016401309662741 99693980672643811390441)
                  ·
                    rfl

theorem cell21_436845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_436845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436845 prefixEnd_436845 := by exact prefixLift 436845
  have htrace : WordTrace (prefixWord ++ tailWord_436845) baseStart_436845 baseEnd_436845 := by
    simpa [prefixWord, tailWord_436845, baseEnd_436845] using wordTrace_append hprefix tailTrace_436845
  have hstable : (prefixWord ++ tailWord_436845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436845).length < 2 ^ (prefixWord ++ tailWord_436845).sum := by decide
  have hdescent : baseEnd_436845 < baseStart_436845 := by decide
  rcases family_descends (prefixWord ++ tailWord_436845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436952 : List Nat := [2, 1, 2, 2, 3, 3, 3, 5]
def baseStart_436952 : Nat := 118140960795 + 436952 * 2 ^ 59
def prefixEnd_436952 : Nat := 4983230072969 + 3 ^ 40 * 436952 * 2
def baseEnd_436952 : Nat := 33239466510145134368963

theorem tailTrace_436952 : CollatzResearch.WordTrace tailWord_436952 prefixEnd_436952 33239466510145134368963 := by
  unfold tailWord_436952
  simp only [CollatzResearch.WordTrace]
  refine ⟨7968474356502502152736555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10624632475336669536982073 7968474356502502152736555)
  ·
    refine ⟨11952711534753753229104833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7968474356502502152736555 11952711534753753229104833)
    ·
      refine ⟨8964533651065314921828625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11952711534753753229104833 8964533651065314921828625)
      ·
        refine ⟨6723400238298986191371469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8964533651065314921828625 6723400238298986191371469)
        ·
          refine ⟨2521275089362119821764301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6723400238298986191371469 2521275089362119821764301)
          ·
            refine ⟨945478158510794933161613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2521275089362119821764301 945478158510794933161613)
            ·
              refine ⟨354554309441548099935605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 945478158510794933161613 354554309441548099935605)
              ·
                refine ⟨33239466510145134368963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 354554309441548099935605 33239466510145134368963)
                ·
                  rfl

theorem cell21_436952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 5].length) (baseStart_436952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_436952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_436952 prefixEnd_436952 := by exact prefixLift 436952
  have htrace : WordTrace (prefixWord ++ tailWord_436952) baseStart_436952 baseEnd_436952 := by
    simpa [prefixWord, tailWord_436952, baseEnd_436952] using wordTrace_append hprefix tailTrace_436952
  have hstable : (prefixWord ++ tailWord_436952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436952).length < 2 ^ (prefixWord ++ tailWord_436952).sum := by decide
  have hdescent : baseEnd_436952 < baseStart_436952 := by decide
  rcases family_descends (prefixWord ++ tailWord_436952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437028 : List Nat := [2, 3, 1, 3, 3, 2, 7]
def baseStart_437028 : Nat := 118140960795 + 437028 * 2 ^ 59
def prefixEnd_437028 : Nat := 4983230072969 + 3 ^ 40 * 437028 * 2
def baseEnd_437028 : Nat := 11081749307319573315563

theorem tailTrace_437028 : CollatzResearch.WordTrace tailWord_437028 prefixEnd_437028 11081749307319573315563 := by
  unfold tailWord_437028
  simp only [CollatzResearch.WordTrace]
  refine ⟨7969860330364834642619869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10626480440486446190159825 7969860330364834642619869)
  ·
    refine ⟨2988697623886812990982451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7969860330364834642619869 2988697623886812990982451)
    ·
      refine ⟨4483046435830219486473677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2988697623886812990982451 4483046435830219486473677)
      ·
        refine ⟨1681142413436332307427629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4483046435830219486473677 1681142413436332307427629)
        ·
          refine ⟨630428405038624615285361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1681142413436332307427629 630428405038624615285361)
          ·
            refine ⟨472821303778968461464021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 630428405038624615285361 472821303778968461464021)
            ·
              refine ⟨11081749307319573315563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 472821303778968461464021 11081749307319573315563)
              ·
                rfl

theorem cell21_437028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 7].length) (baseStart_437028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_437028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_437028 prefixEnd_437028 := by exact prefixLift 437028
  have htrace : WordTrace (prefixWord ++ tailWord_437028) baseStart_437028 baseEnd_437028 := by
    simpa [prefixWord, tailWord_437028, baseEnd_437028] using wordTrace_append hprefix tailTrace_437028
  have hstable : (prefixWord ++ tailWord_437028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437028).length < 2 ^ (prefixWord ++ tailWord_437028).sum := by decide
  have hdescent : baseEnd_437028 < baseStart_437028 := by decide
  rcases family_descends (prefixWord ++ tailWord_437028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437034 : List Nat := [3, 1, 4, 3, 1, 1, 3, 2, 3]
def baseStart_437034 : Nat := 118140960795 + 437034 * 2 ^ 59
def prefixEnd_437034 : Nat := 4983230072969 + 3 ^ 40 * 437034 * 2
def baseEnd_437034 : Nat := 99737113047621482740055

theorem tailTrace_437034 : CollatzResearch.WordTrace tailWord_437034 prefixEnd_437034 99737113047621482740055 := by
  unfold tailWord_437034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3984984874676983077489539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10626626332471954873305437 3984984874676983077489539)
  ·
    refine ⟨5977477312015474616234309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3984984874676983077489539 5977477312015474616234309)
    ·
      refine ⟨1120776996002901490543933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5977477312015474616234309 1120776996002901490543933)
      ·
        refine ⟨420291373501088058953975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1120776996002901490543933 420291373501088058953975)
        ·
          refine ⟨630437060251632088430963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420291373501088058953975 630437060251632088430963)
          ·
            refine ⟨945655590377448132646445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630437060251632088430963 945655590377448132646445)
            ·
              refine ⟨354620846391543049742417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 945655590377448132646445 354620846391543049742417)
              ·
                refine ⟨265965634793657287306813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354620846391543049742417 265965634793657287306813)
                ·
                  refine ⟨99737113047621482740055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265965634793657287306813 99737113047621482740055)
                  ·
                    rfl

theorem cell21_437034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_437034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_437034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_437034 prefixEnd_437034 := by exact prefixLift 437034
  have htrace : WordTrace (prefixWord ++ tailWord_437034) baseStart_437034 baseEnd_437034 := by
    simpa [prefixWord, tailWord_437034, baseEnd_437034] using wordTrace_append hprefix tailTrace_437034
  have hstable : (prefixWord ++ tailWord_437034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437034).length < 2 ^ (prefixWord ++ tailWord_437034).sum := by decide
  have hdescent : baseEnd_437034 < baseStart_437034 := by decide
  rcases family_descends (prefixWord ++ tailWord_437034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437208 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 6]
def baseStart_437208 : Nat := 118140960795 + 437208 * 2 ^ 59
def prefixEnd_437208 : Nat := 4983230072969 + 3 ^ 40 * 437208 * 2
def baseEnd_437208 : Nat := 99776822218235846839699

theorem tailTrace_437208 : CollatzResearch.WordTrace tailWord_437208 prefixEnd_437208 99776822218235846839699 := by
  unfold tailWord_437208
  simp only [CollatzResearch.WordTrace]
  refine ⟨7973142900038780013396139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10630857200051706684528185 7973142900038780013396139)
  ·
    refine ⟨11959714350058170020094209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7973142900038780013396139 11959714350058170020094209)
    ·
      refine ⟨8969785762543627515070657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11959714350058170020094209 8969785762543627515070657)
      ·
        refine ⟨6727339321907720636302993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8969785762543627515070657 6727339321907720636302993)
        ·
          refine ⟨5045504491430790477227245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6727339321907720636302993 5045504491430790477227245)
          ·
            refine ⟨1892064184286546428960217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5045504491430790477227245 1892064184286546428960217)
            ·
              refine ⟨1419048138214909821720163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1892064184286546428960217 1419048138214909821720163)
              ·
                refine ⟨2128572207322364732580245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419048138214909821720163 2128572207322364732580245)
                ·
                  refine ⟨99776822218235846839699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2128572207322364732580245 99776822218235846839699)
                  ·
                    rfl

theorem cell21_437208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_437208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_437208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_437208 prefixEnd_437208 := by exact prefixLift 437208
  have htrace : WordTrace (prefixWord ++ tailWord_437208) baseStart_437208 baseEnd_437208 := by
    simpa [prefixWord, tailWord_437208, baseEnd_437208] using wordTrace_append hprefix tailTrace_437208
  have hstable : (prefixWord ++ tailWord_437208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437208).length < 2 ^ (prefixWord ++ tailWord_437208).sum := by decide
  have hdescent : baseEnd_437208 < baseStart_437208 := by decide
  rcases family_descends (prefixWord ++ tailWord_437208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437287 : List Nat := [1, 1, 7, 1, 1, 2, 1, 2, 5]
def baseStart_437287 : Nat := 118140960795 + 437287 * 2 ^ 59
def prefixEnd_437287 : Nat := 4983230072969 + 3 ^ 40 * 437287 * 2
def baseEnd_437287 : Nat := 99794851094549265022871

theorem tailTrace_437287 : CollatzResearch.WordTrace tailWord_437287 prefixEnd_437287 99794851094549265022871 := by
  unfold tailWord_437287
  simp only [CollatzResearch.WordTrace]
  refine ⟨15949167166791356518918115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10632778111194237679278743 15949167166791356518918115)
  ·
    refine ⟨23923750750187034778377173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15949167166791356518918115 23923750750187034778377173)
    ·
      refine ⟨560712908207508627618215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 23923750750187034778377173 560712908207508627618215)
      ·
        refine ⟨841069362311262941427323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560712908207508627618215 841069362311262941427323)
        ·
          refine ⟨1261604043466894412140985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841069362311262941427323 1261604043466894412140985)
          ·
            refine ⟨946203032600170809105739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1261604043466894412140985 946203032600170809105739)
            ·
              refine ⟨1419304548900256213658609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946203032600170809105739 1419304548900256213658609)
              ·
                refine ⟨1064478411675192160243957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1419304548900256213658609 1064478411675192160243957)
                ·
                  refine ⟨99794851094549265022871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1064478411675192160243957 99794851094549265022871)
                  ·
                    rfl

theorem cell21_437287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 5].length) (baseStart_437287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_437287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_437287 prefixEnd_437287 := by exact prefixLift 437287
  have htrace : WordTrace (prefixWord ++ tailWord_437287) baseStart_437287 baseEnd_437287 := by
    simpa [prefixWord, tailWord_437287, baseEnd_437287] using wordTrace_append hprefix tailTrace_437287
  have hstable : (prefixWord ++ tailWord_437287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437287).length < 2 ^ (prefixWord ++ tailWord_437287).sum := by decide
  have hdescent : baseEnd_437287 < baseStart_437287 := by decide
  rcases family_descends (prefixWord ++ tailWord_437287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437318 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_437318 : Nat := 118140960795 + 437318 * 2 ^ 59
def prefixEnd_437318 : Nat := 4983230072969 + 3 ^ 40 * 437318 * 2
def baseEnd_437318 : Nat := 99801925716900100006141

theorem tailTrace_437318 : CollatzResearch.WordTrace tailWord_437318 prefixEnd_437318 99801925716900100006141 := by
  unfold tailWord_437318
  simp only [CollatzResearch.WordTrace]
  refine ⟨498446807177470275415519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10633531886452699208864405 498446807177470275415519)
  ·
    refine ⟨747670210766205413123279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 498446807177470275415519 747670210766205413123279)
    ·
      refine ⟨1121505316149308119684919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 747670210766205413123279 1121505316149308119684919)
      ·
        refine ⟨1682257974223962179527379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121505316149308119684919 1682257974223962179527379)
        ·
          refine ⟨2523386961335943269291069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682257974223962179527379 2523386961335943269291069)
          ·
            refine ⟨946270110500978725984151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2523386961335943269291069 946270110500978725984151)
            ·
              refine ⟨1419405165751468088976227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946270110500978725984151 1419405165751468088976227)
              ·
                refine ⟨2129107748627202133464341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419405165751468088976227 2129107748627202133464341)
                ·
                  refine ⟨99801925716900100006141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2129107748627202133464341 99801925716900100006141)
                  ·
                    rfl

theorem cell21_437318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_437318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_437318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_437318 prefixEnd_437318 := by exact prefixLift 437318
  have htrace : WordTrace (prefixWord ++ tailWord_437318) baseStart_437318 baseEnd_437318 := by
    simpa [prefixWord, tailWord_437318, baseEnd_437318] using wordTrace_append hprefix tailTrace_437318
  have hstable : (prefixWord ++ tailWord_437318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437318).length < 2 ^ (prefixWord ++ tailWord_437318).sum := by decide
  have hdescent : baseEnd_437318 < baseStart_437318 := by decide
  rcases family_descends (prefixWord ++ tailWord_437318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437329 : List Nat := [1, 2, 2, 1, 3, 1, 3, 3, 5]
def baseStart_437329 : Nat := 118140960795 + 437329 * 2 ^ 59
def prefixEnd_437329 : Nat := 4983230072969 + 3 ^ 40 * 437329 * 2
def baseEnd_437329 : Nat := 99804436066766525322785

theorem tailTrace_437329 : CollatzResearch.WordTrace tailWord_437329 prefixEnd_437329 99804436066766525322785 := by
  unfold tailWord_437329
  simp only [CollatzResearch.WordTrace]
  refine ⟨15950699032639197691947041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10633799355092798461298027 15950699032639197691947041)
  ·
    refine ⟨11963024274479398268960281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15950699032639197691947041 11963024274479398268960281)
    ·
      refine ⟨8972268205859548701720211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11963024274479398268960281 8972268205859548701720211)
      ·
        refine ⟨13458402308789323052580317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8972268205859548701720211 13458402308789323052580317)
        ·
          refine ⟨5046900865795996144717619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13458402308789323052580317 5046900865795996144717619)
          ·
            refine ⟨7570351298693994217076429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5046900865795996144717619 7570351298693994217076429)
            ·
              refine ⟨2838881737010247831403661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7570351298693994217076429 2838881737010247831403661)
              ·
                refine ⟨1064580651378842936776373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2838881737010247831403661 1064580651378842936776373)
                ·
                  refine ⟨99804436066766525322785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1064580651378842936776373 99804436066766525322785)
                  ·
                    rfl

theorem cell21_437329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_437329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_437329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_437329 prefixEnd_437329 := by exact prefixLift 437329
  have htrace : WordTrace (prefixWord ++ tailWord_437329) baseStart_437329 baseEnd_437329 := by
    simpa [prefixWord, tailWord_437329, baseEnd_437329] using wordTrace_append hprefix tailTrace_437329
  have hstable : (prefixWord ++ tailWord_437329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437329).length < 2 ^ (prefixWord ++ tailWord_437329).sum := by decide
  have hdescent : baseEnd_437329 < baseStart_437329 := by decide
  rcases family_descends (prefixWord ++ tailWord_437329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437380 : List Nat := [2, 3, 2, 1, 2, 3, 3, 2, 3]
def baseStart_437380 : Nat := 118140960795 + 437380 * 2 ^ 59
def prefixEnd_437380 : Nat := 4983230072969 + 3 ^ 40 * 437380 * 2
def baseEnd_437380 : Nat := 99816074961601769972681

theorem tailTrace_437380 : CollatzResearch.WordTrace tailWord_437380 prefixEnd_437380 99816074961601769972681 := by
  unfold tailWord_437380
  simp only [CollatzResearch.WordTrace]
  refine ⟨7976279577727216701026797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10635039436969622268035729 7976279577727216701026797)
  ·
    refine ⟨2991104841647706262885049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7976279577727216701026797 2991104841647706262885049)
    ·
      refine ⟨2243328631235779697163787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2991104841647706262885049 2243328631235779697163787)
      ·
        refine ⟨3364992946853669545745681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2243328631235779697163787 3364992946853669545745681)
        ·
          refine ⟨2523744710140252159309261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3364992946853669545745681 2523744710140252159309261)
          ·
            refine ⟨946404266302594559740973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2523744710140252159309261 946404266302594559740973)
            ·
              refine ⟨354901599863472959902865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 946404266302594559740973 354901599863472959902865)
              ·
                refine ⟨266176199897604719927149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354901599863472959902865 266176199897604719927149)
                ·
                  refine ⟨99816074961601769972681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266176199897604719927149 99816074961601769972681)
                  ·
                    rfl

theorem cell21_437380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_437380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_437380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_437380 prefixEnd_437380 := by exact prefixLift 437380
  have htrace : WordTrace (prefixWord ++ tailWord_437380) baseStart_437380 baseEnd_437380 := by
    simpa [prefixWord, tailWord_437380, baseEnd_437380] using wordTrace_append hprefix tailTrace_437380
  have hstable : (prefixWord ++ tailWord_437380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437380).length < 2 ^ (prefixWord ++ tailWord_437380).sum := by decide
  have hdescent : baseEnd_437380 < baseStart_437380 := by decide
  rcases family_descends (prefixWord ++ tailWord_437380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437394 : List Nat := [3, 2, 3, 1, 1, 2, 4, 1, 4]
def baseStart_437394 : Nat := 118140960795 + 437394 * 2 ^ 59
def prefixEnd_437394 : Nat := 4983230072969 + 3 ^ 40 * 437394 * 2
def baseEnd_437394 : Nat := 99819269952340856739319

theorem tailTrace_437394 : CollatzResearch.WordTrace tailWord_437394 prefixEnd_437394 99819269952340856739319 := by
  unfold tailWord_437394
  simp only [CollatzResearch.WordTrace]
  refine ⟨3988267444350928448265809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10635379851602475862042157 3988267444350928448265809)
  ·
    refine ⟨2991200583263196336199357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3988267444350928448265809 2991200583263196336199357)
    ·
      refine ⟨1121700218723698626074759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2991200583263196336199357 1121700218723698626074759)
      ·
        refine ⟨1682550328085547939112139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121700218723698626074759 1682550328085547939112139)
        ·
          refine ⟨2523825492128321908668209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682550328085547939112139 2523825492128321908668209)
          ·
            refine ⟨1892869119096241431501157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2523825492128321908668209 1892869119096241431501157)
            ·
              refine ⟨354912959830545268406467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1892869119096241431501157 354912959830545268406467)
              ·
                refine ⟨532369439745817902609701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354912959830545268406467 532369439745817902609701)
                ·
                  refine ⟨99819269952340856739319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 532369439745817902609701 99819269952340856739319)
                  ·
                    rfl

theorem cell21_437394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_437394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_437394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_437394 prefixEnd_437394 := by exact prefixLift 437394
  have htrace : WordTrace (prefixWord ++ tailWord_437394) baseStart_437394 baseEnd_437394 := by
    simpa [prefixWord, tailWord_437394, baseEnd_437394] using wordTrace_append hprefix tailTrace_437394
  have hstable : (prefixWord ++ tailWord_437394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437394).length < 2 ^ (prefixWord ++ tailWord_437394).sum := by decide
  have hdescent : baseEnd_437394 < baseStart_437394 := by decide
  rcases family_descends (prefixWord ++ tailWord_437394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437405 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 7]
def baseStart_437405 : Nat := 118140960795 + 437405 * 2 ^ 59
def prefixEnd_437405 : Nat := 4983230072969 + 3 ^ 40 * 437405 * 2
def baseEnd_437405 : Nat := 99821780302207282055963

theorem tailTrace_437405 : CollatzResearch.WordTrace tailWord_437405 prefixEnd_437405 99821780302207282055963 := by
  unfold tailWord_437405
  simp only [CollatzResearch.WordTrace]
  refine ⟨15953470980363862671713669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10635647320242575114475779 15953470980363862671713669)
  ·
    refine ⟨2991275808818224250946313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15953470980363862671713669 2991275808818224250946313)
    ·
      refine ⟨2243456856613668188209735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2991275808818224250946313 2243456856613668188209735)
      ·
        refine ⟨3365185284920502282314603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2243456856613668188209735 3365185284920502282314603)
        ·
          refine ⟨5047777927380753423471905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3365185284920502282314603 5047777927380753423471905)
          ·
            refine ⟨3785833445535565067603929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5047777927380753423471905 3785833445535565067603929)
            ·
              refine ⟨2839375084151673800702947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3785833445535565067603929 2839375084151673800702947)
              ·
                refine ⟨4259062626227510701054421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2839375084151673800702947 4259062626227510701054421)
                ·
                  refine ⟨99821780302207282055963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4259062626227510701054421 99821780302207282055963)
                  ·
                    rfl

theorem cell21_437405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_437405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_437405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_437405 prefixEnd_437405 := by exact prefixLift 437405
  have htrace : WordTrace (prefixWord ++ tailWord_437405) baseStart_437405 baseEnd_437405 := by
    simpa [prefixWord, tailWord_437405, baseEnd_437405] using wordTrace_append hprefix tailTrace_437405
  have hstable : (prefixWord ++ tailWord_437405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437405).length < 2 ^ (prefixWord ++ tailWord_437405).sum := by decide
  have hdescent : baseEnd_437405 < baseStart_437405 := by decide
  rcases family_descends (prefixWord ++ tailWord_437405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437439 : List Nat := [1, 1, 2, 2, 2, 2, 6, 2, 3]
def baseStart_437439 : Nat := 118140960795 + 437439 * 2 ^ 59
def prefixEnd_437439 : Nat := 4983230072969 + 3 ^ 40 * 437439 * 2
def baseEnd_437439 : Nat := 99829539565430778489227

theorem tailTrace_437439 : CollatzResearch.WordTrace tailWord_437439 prefixEnd_437439 99829539565430778489227 := by
  unfold tailWord_437439
  simp only [CollatzResearch.WordTrace]
  refine ⟨15954711062240686478451371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10636474041493790985634247 15954711062240686478451371)
  ·
    refine ⟨23932066593361029717677057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15954711062240686478451371 23932066593361029717677057)
    ·
      refine ⟨17949049945020772288257793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23932066593361029717677057 17949049945020772288257793)
      ·
        refine ⟨13461787458765579216193345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17949049945020772288257793 13461787458765579216193345)
        ·
          refine ⟨10096340594074184412145009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13461787458765579216193345 10096340594074184412145009)
          ·
            refine ⟨7572255445555638309108757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10096340594074184412145009 7572255445555638309108757)
            ·
              refine ⟨354949474010420545739473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7572255445555638309108757 354949474010420545739473)
              ·
                refine ⟨266212105507815409304605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354949474010420545739473 266212105507815409304605)
                ·
                  refine ⟨99829539565430778489227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266212105507815409304605 99829539565430778489227)
                  ·
                    rfl

theorem cell21_437439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 3].length) (baseStart_437439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_437439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_437439 prefixEnd_437439 := by exact prefixLift 437439
  have htrace : WordTrace (prefixWord ++ tailWord_437439) baseStart_437439 baseEnd_437439 := by
    simpa [prefixWord, tailWord_437439, baseEnd_437439] using wordTrace_append hprefix tailTrace_437439
  have hstable : (prefixWord ++ tailWord_437439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437439).length < 2 ^ (prefixWord ++ tailWord_437439).sum := by decide
  have hdescent : baseEnd_437439 < baseStart_437439 := by decide
  rcases family_descends (prefixWord ++ tailWord_437439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437442 : List Nat := [3, 5, 1, 1, 2, 2, 1, 6]
def baseStart_437442 : Nat := 118140960795 + 437442 * 2 ^ 59
def prefixEnd_437442 : Nat := 4983230072969 + 3 ^ 40 * 437442 * 2
def baseEnd_437442 : Nat := 33276741402101146646407

theorem tailTrace_437442 : CollatzResearch.WordTrace tailWord_437442 prefixEnd_437442 33276741402101146646407 := by
  unfold tailWord_437442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3988705120307454497702645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10636546987486545327207053 3988705120307454497702645)
  ·
    refine ⟨373941105028823859159623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3988705120307454497702645 373941105028823859159623)
    ·
      refine ⟨560911657543235788739435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373941105028823859159623 560911657543235788739435)
      ·
        refine ⟨841367486314853683109153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560911657543235788739435 841367486314853683109153)
        ·
          refine ⟨631025614736140262331865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 841367486314853683109153 631025614736140262331865)
          ·
            refine ⟨473269211052105196748899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 631025614736140262331865 473269211052105196748899)
            ·
              refine ⟨709903816578157795123349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473269211052105196748899 709903816578157795123349)
              ·
                refine ⟨33276741402101146646407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 709903816578157795123349 33276741402101146646407)
                ·
                  rfl

theorem cell21_437442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_437442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_437442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_437442 prefixEnd_437442 := by exact prefixLift 437442
  have htrace : WordTrace (prefixWord ++ tailWord_437442) baseStart_437442 baseEnd_437442 := by
    simpa [prefixWord, tailWord_437442, baseEnd_437442] using wordTrace_append hprefix tailTrace_437442
  have hstable : (prefixWord ++ tailWord_437442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437442).length < 2 ^ (prefixWord ++ tailWord_437442).sum := by decide
  have hdescent : baseEnd_437442 < baseStart_437442 := by decide
  rcases family_descends (prefixWord ++ tailWord_437442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437495 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 6]
def baseStart_437495 : Nat := 118140960795 + 437495 * 2 ^ 59
def prefixEnd_437495 : Nat := 4983230072969 + 3 ^ 40 * 437495 * 2
def baseEnd_437495 : Nat := 99842319528387125555779

theorem tailTrace_437495 : CollatzResearch.WordTrace tailWord_437495 prefixEnd_437495 99842319528387125555779 := by
  unfold tailWord_437495
  simp only [CollatzResearch.WordTrace]
  refine ⟨15956753550037808042489939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10637835700025205361659959 15956753550037808042489939)
  ·
    refine ⟨23935130325056712063734909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15956753550037808042489939 23935130325056712063734909)
    ·
      refine ⟨8975673871896267023900591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23935130325056712063734909 8975673871896267023900591)
      ·
        refine ⟨13463510807844400535850887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8975673871896267023900591 13463510807844400535850887)
        ·
          refine ⟨20195266211766600803776331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13463510807844400535850887 20195266211766600803776331)
          ·
            refine ⟨30292899317649901205664497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20195266211766600803776331 30292899317649901205664497)
            ·
              refine ⟨22719674488237425904248373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30292899317649901205664497 22719674488237425904248373)
              ·
                refine ⟨2129969483272258678523285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22719674488237425904248373 2129969483272258678523285)
                ·
                  refine ⟨99842319528387125555779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2129969483272258678523285 99842319528387125555779)
                  ·
                    rfl

theorem cell21_437495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 6].length) (baseStart_437495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_437495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_437495 prefixEnd_437495 := by exact prefixLift 437495
  have htrace : WordTrace (prefixWord ++ tailWord_437495) baseStart_437495 baseEnd_437495 := by
    simpa [prefixWord, tailWord_437495, baseEnd_437495] using wordTrace_append hprefix tailTrace_437495
  have hstable : (prefixWord ++ tailWord_437495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437495).length < 2 ^ (prefixWord ++ tailWord_437495).sum := by decide
  have hdescent : baseEnd_437495 < baseStart_437495 := by decide
  rcases family_descends (prefixWord ++ tailWord_437495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437498 : List Nat := [3, 1, 1, 1, 1, 4, 1, 6, 3]
def baseStart_437498 : Nat := 118140960795 + 437498 * 2 ^ 59
def prefixEnd_437498 : Nat := 4983230072969 + 3 ^ 40 * 437498 * 2
def baseEnd_437498 : Nat := 99843004169259787005773

theorem tailTrace_437498 : CollatzResearch.WordTrace tailWord_437498 prefixEnd_437498 99843004169259787005773 := by
  unfold tailWord_437498
  simp only [CollatzResearch.WordTrace]
  refine ⟨3989215742256734888712287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10637908646017959703232765 3989215742256734888712287)
  ·
    refine ⟨5983823613385102333068431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3989215742256734888712287 5983823613385102333068431)
    ·
      refine ⟨8975735420077653499602647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5983823613385102333068431 8975735420077653499602647)
      ·
        refine ⟨13463603130116480249403971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8975735420077653499602647 13463603130116480249403971)
        ·
          refine ⟨20195404695174720374105957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13463603130116480249403971 20195404695174720374105957)
          ·
            refine ⟨3786638380345260070144867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20195404695174720374105957 3786638380345260070144867)
            ·
              refine ⟨5679957570517890105217301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3786638380345260070144867 5679957570517890105217301)
              ·
                refine ⟨266248011118026098682061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5679957570517890105217301 266248011118026098682061)
                ·
                  refine ⟨99843004169259787005773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266248011118026098682061 99843004169259787005773)
                  ·
                    rfl

theorem cell21_437498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_437498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_437498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_437498 prefixEnd_437498 := by exact prefixLift 437498
  have htrace : WordTrace (prefixWord ++ tailWord_437498) baseStart_437498 baseEnd_437498 := by
    simpa [prefixWord, tailWord_437498, baseEnd_437498] using wordTrace_append hprefix tailTrace_437498
  have hstable : (prefixWord ++ tailWord_437498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437498).length < 2 ^ (prefixWord ++ tailWord_437498).sum := by decide
  have hdescent : baseEnd_437498 < baseStart_437498 := by decide
  rcases family_descends (prefixWord ++ tailWord_437498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437549 : List Nat := [1, 5, 3, 1, 1, 2, 3, 2, 3]
def baseStart_437549 : Nat := 118140960795 + 437549 * 2 ^ 59
def prefixEnd_437549 : Nat := 4983230072969 + 3 ^ 40 * 437549 * 2
def baseEnd_437549 : Nat := 99854643064095031655669

theorem tailTrace_437549 : CollatzResearch.WordTrace tailWord_437549 prefixEnd_437549 99854643064095031655669 := by
  unfold tailWord_437549
  simp only [CollatzResearch.WordTrace]
  refine ⟨15958723091842175264955701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10639148727894783509970467 15958723091842175264955701)
  ·
    refine ⟨1496130289860203931089597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15958723091842175264955701 1496130289860203931089597)
    ·
      refine ⟨561048858697576474158599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1496130289860203931089597 561048858697576474158599)
      ·
        refine ⟨841573288046364711237899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561048858697576474158599 841573288046364711237899)
        ·
          refine ⟨1262359932069547066856849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841573288046364711237899 1262359932069547066856849)
          ·
            refine ⟨946769949052160300142637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1262359932069547066856849 946769949052160300142637)
            ·
              refine ⟨355038730894560112553489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 946769949052160300142637 355038730894560112553489)
              ·
                refine ⟨266279048170920084415117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355038730894560112553489 266279048170920084415117)
                ·
                  refine ⟨99854643064095031655669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266279048170920084415117 99854643064095031655669)
                  ·
                    rfl

theorem cell21_437549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_437549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_437549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_437549 prefixEnd_437549 := by exact prefixLift 437549
  have htrace : WordTrace (prefixWord ++ tailWord_437549) baseStart_437549 baseEnd_437549 := by
    simpa [prefixWord, tailWord_437549, baseEnd_437549] using wordTrace_append hprefix tailTrace_437549
  have hstable : (prefixWord ++ tailWord_437549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437549).length < 2 ^ (prefixWord ++ tailWord_437549).sum := by decide
  have hdescent : baseEnd_437549 < baseStart_437549 := by decide
  rcases family_descends (prefixWord ++ tailWord_437549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437681 : List Nat := [1, 2, 2, 4, 1, 1, 5, 1, 4]
def baseStart_437681 : Nat := 118140960795 + 437681 * 2 ^ 59
def prefixEnd_437681 : Nat := 4983230072969 + 3 ^ 40 * 437681 * 2
def baseEnd_437681 : Nat := 99884767262492135455399

theorem tailTrace_437681 : CollatzResearch.WordTrace tailWord_437681 prefixEnd_437681 99884767262492135455399 := by
  unfold tailWord_437681
  simp only [CollatzResearch.WordTrace]
  refine ⟨15963537527363961808760897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10642358351575974539173931 15963537527363961808760897)
  ·
    refine ⟨11972653145522971356570673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15963537527363961808760897 11972653145522971356570673)
    ·
      refine ⟨8979489859142228517428005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11972653145522971356570673 8979489859142228517428005)
      ·
        refine ⟨1683654348589167847017751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8979489859142228517428005 1683654348589167847017751)
        ·
          refine ⟨2525481522883751770526627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1683654348589167847017751 2525481522883751770526627)
          ·
            refine ⟨3788222284325627655789941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525481522883751770526627 3788222284325627655789941)
            ·
              refine ⟨355145839155527592730307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3788222284325627655789941 355145839155527592730307)
              ·
                refine ⟨532718758733291389095461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355145839155527592730307 532718758733291389095461)
                ·
                  refine ⟨99884767262492135455399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 532718758733291389095461 99884767262492135455399)
                  ·
                    rfl

theorem cell21_437681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 4].length) (baseStart_437681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_437681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_437681 prefixEnd_437681 := by exact prefixLift 437681
  have htrace : WordTrace (prefixWord ++ tailWord_437681) baseStart_437681 baseEnd_437681 := by
    simpa [prefixWord, tailWord_437681, baseEnd_437681] using wordTrace_append hprefix tailTrace_437681
  have hstable : (prefixWord ++ tailWord_437681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437681).length < 2 ^ (prefixWord ++ tailWord_437681).sum := by decide
  have hdescent : baseEnd_437681 < baseStart_437681 := by decide
  rcases family_descends (prefixWord ++ tailWord_437681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437861 : List Nat := [1, 3, 1, 3, 3, 1, 2, 2, 5]
def baseStart_437861 : Nat := 118140960795 + 437861 * 2 ^ 59
def prefixEnd_437861 : Nat := 4983230072969 + 3 ^ 40 * 437861 * 2
def baseEnd_437861 : Nat := 99925845714851822455031

theorem tailTrace_437861 : CollatzResearch.WordTrace tailWord_437861 prefixEnd_437861 99925845714851822455031 := by
  unfold tailWord_437861
  simp only [CollatzResearch.WordTrace]
  refine ⟨15970102666711852550313437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10646735111141235033542291 15970102666711852550313437)
  ·
    refine ⟨5988788500016944706367539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15970102666711852550313437 5988788500016944706367539)
    ·
      refine ⟨8983182750025417059551309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5988788500016944706367539 8983182750025417059551309)
      ·
        refine ⟨3368693531259531397331741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8983182750025417059551309 3368693531259531397331741)
        ·
          refine ⟨1263260074222324273999403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3368693531259531397331741 1263260074222324273999403)
          ·
            refine ⟨1894890111333486410999105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263260074222324273999403 1894890111333486410999105)
            ·
              refine ⟨1421167583500114808249329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1894890111333486410999105 1421167583500114808249329)
              ·
                refine ⟨1065875687625086106186997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1421167583500114808249329 1065875687625086106186997)
                ·
                  refine ⟨99925845714851822455031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1065875687625086106186997 99925845714851822455031)
                  ·
                    rfl

theorem cell21_437861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_437861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_437861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_437861 prefixEnd_437861 := by exact prefixLift 437861
  have htrace : WordTrace (prefixWord ++ tailWord_437861) baseStart_437861 baseEnd_437861 := by
    simpa [prefixWord, tailWord_437861, baseEnd_437861] using wordTrace_append hprefix tailTrace_437861
  have hstable : (prefixWord ++ tailWord_437861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437861).length < 2 ^ (prefixWord ++ tailWord_437861).sum := by decide
  have hdescent : baseEnd_437861 < baseStart_437861 := by decide
  rcases family_descends (prefixWord ++ tailWord_437861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437864 : List Nat := [2, 1, 4, 3, 1, 3, 2, 5]
def baseStart_437864 : Nat := 118140960795 + 437864 * 2 ^ 59
def prefixEnd_437864 : Nat := 4983230072969 + 3 ^ 40 * 437864 * 2
def baseEnd_437864 : Nat := 33308843451908161301675

theorem tailTrace_437864 : CollatzResearch.WordTrace tailWord_437864 prefixEnd_437864 33308843451908161301675 := by
  unfold tailWord_437864
  simp only [CollatzResearch.WordTrace]
  refine ⟨7985106042850492031336323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10646808057133989375115097 7985106042850492031336323)
  ·
    refine ⟨11977659064275738047004485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7985106042850492031336323 11977659064275738047004485)
    ·
      refine ⟨2245811074551700883813341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11977659064275738047004485 2245811074551700883813341)
      ·
        refine ⟨842179152956887831430003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2245811074551700883813341 842179152956887831430003)
        ·
          refine ⟨1263268729435331747145005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842179152956887831430003 1263268729435331747145005)
          ·
            refine ⟨473725773538249405179377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1263268729435331747145005 473725773538249405179377)
            ·
              refine ⟨355294330153687053884533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473725773538249405179377 355294330153687053884533)
              ·
                refine ⟨33308843451908161301675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 355294330153687053884533 33308843451908161301675)
                ·
                  rfl

theorem cell21_437864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 5].length) (baseStart_437864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_437864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_437864 prefixEnd_437864 := by exact prefixLift 437864
  have htrace : WordTrace (prefixWord ++ tailWord_437864) baseStart_437864 baseEnd_437864 := by
    simpa [prefixWord, tailWord_437864, baseEnd_437864] using wordTrace_append hprefix tailTrace_437864
  have hstable : (prefixWord ++ tailWord_437864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437864).length < 2 ^ (prefixWord ++ tailWord_437864).sum := by decide
  have hdescent : baseEnd_437864 < baseStart_437864 := by decide
  rcases family_descends (prefixWord ++ tailWord_437864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437895 : List Nat := [1, 1, 4, 2, 1, 4, 3, 2, 3]
def baseStart_437895 : Nat := 118140960795 + 437895 * 2 ^ 59
def prefixEnd_437895 : Nat := 4983230072969 + 3 ^ 40 * 437895 * 2
def baseEnd_437895 : Nat := 99933604978075318888295

theorem tailTrace_437895 : CollatzResearch.WordTrace tailWord_437895 prefixEnd_437895 99933604978075318888295 := by
  unfold tailWord_437895
  simp only [CollatzResearch.WordTrace]
  refine ⟨15971342748588676357051139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10647561832392450904700759 15971342748588676357051139)
  ·
    refine ⟨23957014122883014535576709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15971342748588676357051139 23957014122883014535576709)
    ·
      refine ⟨4491940148040565225420633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23957014122883014535576709 4491940148040565225420633)
      ·
        refine ⟨3368955111030423919065475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4491940148040565225420633 3368955111030423919065475)
        ·
          refine ⟨5053432666545635878598213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3368955111030423919065475 5053432666545635878598213)
          ·
            refine ⟨947518624977306727237165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5053432666545635878598213 947518624977306727237165)
            ·
              refine ⟨355319484366490022713937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 947518624977306727237165 355319484366490022713937)
              ·
                refine ⟨266489613274867517035453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355319484366490022713937 266489613274867517035453)
                ·
                  refine ⟨99933604978075318888295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266489613274867517035453 99933604978075318888295)
                  ·
                    rfl

theorem cell21_437895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 3].length) (baseStart_437895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_437895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_437895 prefixEnd_437895 := by exact prefixLift 437895
  have htrace : WordTrace (prefixWord ++ tailWord_437895) baseStart_437895 baseEnd_437895 := by
    simpa [prefixWord, tailWord_437895, baseEnd_437895] using wordTrace_append hprefix tailTrace_437895
  have hstable : (prefixWord ++ tailWord_437895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437895).length < 2 ^ (prefixWord ++ tailWord_437895).sum := by decide
  have hdescent : baseEnd_437895 < baseStart_437895 := by decide
  rcases family_descends (prefixWord ++ tailWord_437895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438027 : List Nat := [1, 1, 1, 1, 5, 1, 2, 5, 4]
def baseStart_438027 : Nat := 118140960795 + 438027 * 2 ^ 59
def prefixEnd_438027 : Nat := 4983230072969 + 3 ^ 40 * 438027 * 2
def baseEnd_438027 : Nat := 99963729176472422688025

theorem tailTrace_438027 : CollatzResearch.WordTrace tailWord_438027 prefixEnd_438027 99963729176472422688025 := by
  unfold tailWord_438027
  simp only [CollatzResearch.WordTrace]
  refine ⟨15976157184110462900856335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10650771456073641933904223 15976157184110462900856335)
  ·
    refine ⟨23964235776165694351284503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15976157184110462900856335 23964235776165694351284503)
    ·
      refine ⟨35946353664248541526926755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23964235776165694351284503 35946353664248541526926755)
      ·
        refine ⟨53919530496372812290390133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35946353664248541526926755 53919530496372812290390133)
        ·
          refine ⟨5054955984034951152224075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53919530496372812290390133 5054955984034951152224075)
          ·
            refine ⟨7582433976052426728336113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5054955984034951152224075 7582433976052426728336113)
            ·
              refine ⟨5686825482039320046252085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7582433976052426728336113 5686825482039320046252085)
              ·
                refine ⟨533139888941186254336133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5686825482039320046252085 533139888941186254336133)
                ·
                  refine ⟨99963729176472422688025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 533139888941186254336133 99963729176472422688025)
                  ·
                    rfl

theorem cell21_438027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 4].length) (baseStart_438027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_438027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_438027 prefixEnd_438027 := by exact prefixLift 438027
  have htrace : WordTrace (prefixWord ++ tailWord_438027) baseStart_438027 baseEnd_438027 := by
    simpa [prefixWord, tailWord_438027, baseEnd_438027] using wordTrace_append hprefix tailTrace_438027
  have hstable : (prefixWord ++ tailWord_438027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438027).length < 2 ^ (prefixWord ++ tailWord_438027).sum := by decide
  have hdescent : baseEnd_438027 < baseStart_438027 := by decide
  rcases family_descends (prefixWord ++ tailWord_438027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438078 : List Nat := [4, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_438078 : Nat := 118140960795 + 438078 * 2 ^ 59
def prefixEnd_438078 : Nat := 4983230072969 + 3 ^ 40 * 438078 * 2
def baseEnd_438078 : Nat := 99975368071307667337921

theorem tailTrace_438078 : CollatzResearch.WordTrace tailWord_438078 prefixEnd_438078 99975368071307667337921 := by
  unfold tailWord_438078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1997252163365712326370361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10652011537950465740641925 1997252163365712326370361)
  ·
    refine ⟨1497939122524284244777771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1997252163365712326370361 1497939122524284244777771)
    ·
      refine ⟨2246908683786426367166657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1497939122524284244777771 2246908683786426367166657)
      ·
        refine ⟨1685181512839819775374993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2246908683786426367166657 1685181512839819775374993)
        ·
          refine ⟨1263886134629864831531245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1685181512839819775374993 1263886134629864831531245)
          ·
            refine ⟨473957300486199311824217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1263886134629864831531245 473957300486199311824217)
            ·
              refine ⟨355467975364649483868163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473957300486199311824217 355467975364649483868163)
              ·
                refine ⟨533201963046974225802245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355467975364649483868163 533201963046974225802245)
                ·
                  refine ⟨99975368071307667337921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 533201963046974225802245 99975368071307667337921)
                  ·
                    rfl

theorem cell21_438078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_438078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_438078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_438078 prefixEnd_438078 := by exact prefixLift 438078
  have htrace : WordTrace (prefixWord ++ tailWord_438078) baseStart_438078 baseEnd_438078 := by
    simpa [prefixWord, tailWord_438078, baseEnd_438078] using wordTrace_append hprefix tailTrace_438078
  have hstable : (prefixWord ++ tailWord_438078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438078).length < 2 ^ (prefixWord ++ tailWord_438078).sum := by decide
  have hdescent : baseEnd_438078 < baseStart_438078 := by decide
  rcases family_descends (prefixWord ++ tailWord_438078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438120 : List Nat := [2, 1, 4, 2, 1, 1, 4, 2, 4]
def baseStart_438120 : Nat := 118140960795 + 438120 * 2 ^ 59
def prefixEnd_438120 : Nat := 4983230072969 + 3 ^ 40 * 438120 * 2
def baseEnd_438120 : Nat := 99984953043524927637835

theorem tailTrace_438120 : CollatzResearch.WordTrace tailWord_438120 prefixEnd_438120 99984953043524927637835 := by
  unfold tailWord_438120
  simp only [CollatzResearch.WordTrace]
  refine ⟨7989774586386769891995907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10653032781849026522661209 7989774586386769891995907)
  ·
    refine ⟨11984661879580154837993861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7989774586386769891995907 11984661879580154837993861)
    ·
      refine ⟨2247124102421279032123849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11984661879580154837993861 2247124102421279032123849)
      ·
        refine ⟨1685343076815959274092887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2247124102421279032123849 1685343076815959274092887)
        ·
          refine ⟨2528014615223938911139331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1685343076815959274092887 2528014615223938911139331)
          ·
            refine ⟨3792021922835908366708997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2528014615223938911139331 3792021922835908366708997)
            ·
              refine ⟨711004110531732818757937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3792021922835908366708997 711004110531732818757937)
              ·
                refine ⟨533253082898799614068453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 711004110531732818757937 533253082898799614068453)
                ·
                  refine ⟨99984953043524927637835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 533253082898799614068453 99984953043524927637835)
                  ·
                    rfl

theorem cell21_438120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_438120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_438120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_438120 prefixEnd_438120 := by exact prefixLift 438120
  have htrace : WordTrace (prefixWord ++ tailWord_438120) baseStart_438120 baseEnd_438120 := by
    simpa [prefixWord, tailWord_438120, baseEnd_438120] using wordTrace_append hprefix tailTrace_438120
  have hstable : (prefixWord ++ tailWord_438120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438120).length < 2 ^ (prefixWord ++ tailWord_438120).sum := by decide
  have hdescent : baseEnd_438120 < baseStart_438120 := by decide
  rcases family_descends (prefixWord ++ tailWord_438120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438148 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 7]
def baseStart_438148 : Nat := 118140960795 + 438148 * 2 ^ 59
def prefixEnd_438148 : Nat := 4983230072969 + 3 ^ 40 * 438148 * 2
def baseEnd_438148 : Nat := 99991343025003101171111

theorem tailTrace_438148 : CollatzResearch.WordTrace tailWord_438148 prefixEnd_438148 99991343025003101171111 := by
  unfold tailWord_438148
  simp only [CollatzResearch.WordTrace]
  refine ⟨7990285208336050283005549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10653713611114733710674065 7990285208336050283005549)
  ·
    refine ⟨2996356953126018856127081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7990285208336050283005549 2996356953126018856127081)
    ·
      refine ⟨2247267714844514142095311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2996356953126018856127081 2247267714844514142095311)
      ·
        refine ⟨3370901572266771213142967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2247267714844514142095311 3370901572266771213142967)
        ·
          refine ⟨5056352358400156819714451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3370901572266771213142967 5056352358400156819714451)
          ·
            refine ⟨7584528537600235229571677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5056352358400156819714451 7584528537600235229571677)
            ·
              refine ⟨2844198201600088211089379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7584528537600235229571677 2844198201600088211089379)
              ·
                refine ⟨4266297302400132316634069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2844198201600088211089379 4266297302400132316634069)
                ·
                  refine ⟨99991343025003101171111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4266297302400132316634069 99991343025003101171111)
                  ·
                    rfl

theorem cell21_438148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_438148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_438148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_438148 prefixEnd_438148 := by exact prefixLift 438148
  have htrace : WordTrace (prefixWord ++ tailWord_438148) baseStart_438148 baseEnd_438148 := by
    simpa [prefixWord, tailWord_438148, baseEnd_438148] using wordTrace_append hprefix tailTrace_438148
  have hstable : (prefixWord ++ tailWord_438148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438148).length < 2 ^ (prefixWord ++ tailWord_438148).sum := by decide
  have hdescent : baseEnd_438148 < baseStart_438148 := by decide
  rcases family_descends (prefixWord ++ tailWord_438148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438151 : List Nat := [1, 1, 4, 2, 4, 1, 3, 5]
def baseStart_438151 : Nat := 118140960795 + 438151 * 2 ^ 59
def prefixEnd_438151 : Nat := 4983230072969 + 3 ^ 40 * 438151 * 2
def baseEnd_438151 : Nat := 33330675888625254207035

theorem tailTrace_438151 : CollatzResearch.WordTrace tailWord_438151 prefixEnd_438151 33330675888625254207035 := by
  unfold tailWord_438151
  simp only [CollatzResearch.WordTrace]
  refine ⟨15980679835661232078370307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10653786557107488052246871 15980679835661232078370307)
  ·
    refine ⟨23971019753491848117555461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15980679835661232078370307 23971019753491848117555461)
    ·
      refine ⟨4494566203779721522041649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23971019753491848117555461 4494566203779721522041649)
      ·
        refine ⟨3370924652834791141531237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4494566203779721522041649 3370924652834791141531237)
        ·
          refine ⟨632048372406523339037107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3370924652834791141531237 632048372406523339037107)
          ·
            refine ⟨948072558609785008555661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632048372406523339037107 948072558609785008555661)
            ·
              refine ⟨355527209478669378208373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 948072558609785008555661 355527209478669378208373)
              ·
                refine ⟨33330675888625254207035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 355527209478669378208373 33330675888625254207035)
                ·
                  rfl

theorem cell21_438151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 5].length) (baseStart_438151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_438151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_438151 prefixEnd_438151 := by exact prefixLift 438151
  have htrace : WordTrace (prefixWord ++ tailWord_438151) baseStart_438151 baseEnd_438151 := by
    simpa [prefixWord, tailWord_438151, baseEnd_438151] using wordTrace_append hprefix tailTrace_438151
  have hstable : (prefixWord ++ tailWord_438151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438151).length < 2 ^ (prefixWord ++ tailWord_438151).sum := by decide
  have hdescent : baseEnd_438151 < baseStart_438151 := by decide
  rcases family_descends (prefixWord ++ tailWord_438151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438241 : List Nat := [1, 2, 3, 1, 2, 1, 2, 6, 3]
def baseStart_438241 : Nat := 118140960795 + 438241 * 2 ^ 59
def prefixEnd_438241 : Nat := 4983230072969 + 3 ^ 40 * 438241 * 2
def baseEnd_438241 : Nat := 100012566892055606120921

theorem tailTrace_438241 : CollatzResearch.WordTrace tailWord_438241 prefixEnd_438241 100012566892055606120921 := by
  unfold tailWord_438241
  simp only [CollatzResearch.WordTrace]
  refine ⟨15983962405335177449146577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10655974936890118299431051 15983962405335177449146577)
  ·
    refine ⟨11987971804001383086859933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15983962405335177449146577 11987971804001383086859933)
    ·
      refine ⟨4495489426500518657572475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11987971804001383086859933 4495489426500518657572475)
      ·
        refine ⟨6743234139750777986358713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4495489426500518657572475 6743234139750777986358713)
        ·
          refine ⟨5057425604813083489769035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6743234139750777986358713 5057425604813083489769035)
          ·
            refine ⟨7586138407219625234653553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5057425604813083489769035 7586138407219625234653553)
            ·
              refine ⟨5689603805414718925990165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7586138407219625234653553 5689603805414718925990165)
              ·
                refine ⟨266700178378814949655789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5689603805414718925990165 266700178378814949655789)
                ·
                  refine ⟨100012566892055606120921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266700178378814949655789 100012566892055606120921)
                  ·
                    rfl

theorem cell21_438241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 3].length) (baseStart_438241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_438241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_438241 prefixEnd_438241 := by exact prefixLift 438241
  have htrace : WordTrace (prefixWord ++ tailWord_438241) baseStart_438241 baseEnd_438241 := by
    simpa [prefixWord, tailWord_438241, baseEnd_438241] using wordTrace_append hprefix tailTrace_438241
  have hstable : (prefixWord ++ tailWord_438241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438241).length < 2 ^ (prefixWord ++ tailWord_438241).sum := by decide
  have hdescent : baseEnd_438241 < baseStart_438241 := by decide
  rcases family_descends (prefixWord ++ tailWord_438241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438255 : List Nat := [1, 1, 2, 1, 4, 2, 3, 3, 4]
def baseStart_438255 : Nat := 118140960795 + 438255 * 2 ^ 59
def prefixEnd_438255 : Nat := 4983230072969 + 3 ^ 40 * 438255 * 2
def baseEnd_438255 : Nat := 100015761882794692887559

theorem tailTrace_438255 : CollatzResearch.WordTrace tailWord_438255 prefixEnd_438255 100015761882794692887559 := by
  unfold tailWord_438255
  simp only [CollatzResearch.WordTrace]
  refine ⟨15984473027284457840156219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10656315351522971893437479 15984473027284457840156219)
  ·
    refine ⟨23976709540926686760234329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15984473027284457840156219 23976709540926686760234329)
    ·
      refine ⟨17982532155695015070175747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23976709540926686760234329 17982532155695015070175747)
      ·
        refine ⟨26973798233542522605263621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17982532155695015070175747 26973798233542522605263621)
        ·
          refine ⟨5057587168789222988486929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26973798233542522605263621 5057587168789222988486929)
          ·
            refine ⟨3793190376591917241365197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5057587168789222988486929 3793190376591917241365197)
            ·
              refine ⟨1422446391221968965511949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3793190376591917241365197 1422446391221968965511949)
              ·
                refine ⟨533417396708238362066981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1422446391221968965511949 533417396708238362066981)
                ·
                  refine ⟨100015761882794692887559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 533417396708238362066981 100015761882794692887559)
                  ·
                    rfl

theorem cell21_438255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 4].length) (baseStart_438255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_438255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_438255 prefixEnd_438255 := by exact prefixLift 438255
  have htrace : WordTrace (prefixWord ++ tailWord_438255) baseStart_438255 baseEnd_438255 := by
    simpa [prefixWord, tailWord_438255, baseEnd_438255] using wordTrace_append hprefix tailTrace_438255
  have hstable : (prefixWord ++ tailWord_438255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438255).length < 2 ^ (prefixWord ++ tailWord_438255).sum := by decide
  have hdescent : baseEnd_438255 < baseStart_438255 := by decide
  rcases family_descends (prefixWord ++ tailWord_438255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438269 : List Nat := [1, 4, 1, 1, 1, 2, 4, 7]
def baseStart_438269 : Nat := 118140960795 + 438269 * 2 ^ 59
def prefixEnd_438269 : Nat := 4983230072969 + 3 ^ 40 * 438269 * 2
def baseEnd_438269 : Nat := 33339652291177926551399

theorem tailTrace_438269 : CollatzResearch.WordTrace tailWord_438269 prefixEnd_438269 33339652291177926551399 := by
  unfold tailWord_438269
  simp only [CollatzResearch.WordTrace]
  refine ⟨15984983649233738231165861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10656655766155825487443907 15984983649233738231165861)
  ·
    refine ⟨2997184434231325918343599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15984983649233738231165861 2997184434231325918343599)
    ·
      refine ⟨4495776651346988877515399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2997184434231325918343599 4495776651346988877515399)
      ·
        refine ⟨6743664977020483316273099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4495776651346988877515399 6743664977020483316273099)
        ·
          refine ⟨10115497465530724974409649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6743664977020483316273099 10115497465530724974409649)
          ·
            refine ⟨7586623099148043730807237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10115497465530724974409649 7586623099148043730807237)
            ·
              refine ⟨1422491831090258199526357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7586623099148043730807237 1422491831090258199526357)
              ·
                refine ⟨33339652291177926551399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1422491831090258199526357 33339652291177926551399)
                ·
                  rfl

theorem cell21_438269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 7].length) (baseStart_438269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_438269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_438269 prefixEnd_438269 := by exact prefixLift 438269
  have htrace : WordTrace (prefixWord ++ tailWord_438269) baseStart_438269 baseEnd_438269 := by
    simpa [prefixWord, tailWord_438269, baseEnd_438269] using wordTrace_append hprefix tailTrace_438269
  have hstable : (prefixWord ++ tailWord_438269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438269).length < 2 ^ (prefixWord ++ tailWord_438269).sum := by decide
  have hdescent : baseEnd_438269 < baseStart_438269 := by decide
  rcases family_descends (prefixWord ++ tailWord_438269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438292 : List Nat := [2, 4, 3, 2, 1, 1, 1, 4, 3]
def baseStart_438292 : Nat := 118140960795 + 438292 * 2 ^ 59
def prefixEnd_438292 : Nat := 4983230072969 + 3 ^ 40 * 438292 * 2
def baseEnd_438292 : Nat := 100024205786890850770817

theorem tailTrace_438292 : CollatzResearch.WordTrace tailWord_438292 prefixEnd_438292 100024205786890850770817 := by
  unfold tailWord_438292
  simp only [CollatzResearch.WordTrace]
  refine ⟨7992911264075206579626565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10657215018766942106168753 7992911264075206579626565)
  ·
    refine ⟨1498670862014101233679981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7992911264075206579626565 1498670862014101233679981)
    ·
      refine ⟨562001573255287962629993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1498670862014101233679981 562001573255287962629993)
      ·
        refine ⟨421501179941465971972495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 562001573255287962629993 421501179941465971972495)
        ·
          refine ⟨632251769912198957958743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421501179941465971972495 632251769912198957958743)
          ·
            refine ⟨948377654868298436938115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632251769912198957958743 948377654868298436938115)
            ·
              refine ⟨1422566482302447655407173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948377654868298436938115 1422566482302447655407173)
              ·
                refine ⟨266731215431708935388845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1422566482302447655407173 266731215431708935388845)
                ·
                  refine ⟨100024205786890850770817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266731215431708935388845 100024205786890850770817)
                  ·
                    rfl

theorem cell21_438292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_438292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_438292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_438292 prefixEnd_438292 := by exact prefixLift 438292
  have htrace : WordTrace (prefixWord ++ tailWord_438292) baseStart_438292 baseEnd_438292 := by
    simpa [prefixWord, tailWord_438292, baseEnd_438292] using wordTrace_append hprefix tailTrace_438292
  have hstable : (prefixWord ++ tailWord_438292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438292).length < 2 ^ (prefixWord ++ tailWord_438292).sum := by decide
  have hdescent : baseEnd_438292 < baseStart_438292 := by decide
  rcases family_descends (prefixWord ++ tailWord_438292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438421 : List Nat := [1, 3, 2, 1, 1, 1, 6, 6]
def baseStart_438421 : Nat := 118140960795 + 438421 * 2 ^ 59
def prefixEnd_438421 : Nat := 4983230072969 + 3 ^ 40 * 438421 * 2
def baseEnd_438421 : Nat := 33351215114805097706851

theorem tailTrace_438421 : CollatzResearch.WordTrace tailWord_438421 prefixEnd_438421 33351215114805097706851 := by
  unfold tailWord_438421
  simp only [CollatzResearch.WordTrace]
  refine ⟨15990527544683068190699117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10660351696455378793799411 15990527544683068190699117)
  ·
    refine ⟨5996447829256150571512169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15990527544683068190699117 5996447829256150571512169)
    ·
      refine ⟨4497335871942112928634127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5996447829256150571512169 4497335871942112928634127)
      ·
        refine ⟨6746003807913169392951191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4497335871942112928634127 6746003807913169392951191)
        ·
          refine ⟨10119005711869754089426787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6746003807913169392951191 10119005711869754089426787)
          ·
            refine ⟨15178508567804631134140181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10119005711869754089426787 15178508567804631134140181)
            ·
              refine ⟨711492589115842084412821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15178508567804631134140181 711492589115842084412821)
              ·
                refine ⟨33351215114805097706851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 711492589115842084412821 33351215114805097706851)
                ·
                  rfl

theorem cell21_438421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 6].length) (baseStart_438421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_438421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_438421 prefixEnd_438421 := by exact prefixLift 438421
  have htrace : WordTrace (prefixWord ++ tailWord_438421) baseStart_438421 baseEnd_438421 := by
    simpa [prefixWord, tailWord_438421, baseEnd_438421] using wordTrace_append hprefix tailTrace_438421
  have hstable : (prefixWord ++ tailWord_438421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438421).length < 2 ^ (prefixWord ++ tailWord_438421).sum := by decide
  have hdescent : baseEnd_438421 < baseStart_438421 := by decide
  rcases family_descends (prefixWord ++ tailWord_438421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438424 : List Nat := [2, 1, 2, 4, 3, 1, 1, 3, 4]
def baseStart_438424 : Nat := 118140960795 + 438424 * 2 ^ 59
def prefixEnd_438424 : Nat := 4983230072969 + 3 ^ 40 * 438424 * 2
def baseEnd_438424 : Nat := 100054329985287954570547

theorem tailTrace_438424 : CollatzResearch.WordTrace tailWord_438424 prefixEnd_438424 100054329985287954570547 := by
  unfold tailWord_438424
  simp only [CollatzResearch.WordTrace]
  refine ⟨7995318481836099851529163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10660424642448133135372217 7995318481836099851529163)
  ·
    refine ⟨11992977722754149777293745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7995318481836099851529163 11992977722754149777293745)
    ·
      refine ⟨8994733292065612332970309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11992977722754149777293745 8994733292065612332970309)
      ·
        refine ⟨1686512492262302312431933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8994733292065612332970309 1686512492262302312431933)
        ·
          refine ⟨632442184598363367161975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1686512492262302312431933 632442184598363367161975)
          ·
            refine ⟨948663276897545050742963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632442184598363367161975 948663276897545050742963)
            ·
              refine ⟨1422994915346317576114445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948663276897545050742963 1422994915346317576114445)
              ·
                refine ⟨533623093254869091042917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1422994915346317576114445 533623093254869091042917)
                ·
                  refine ⟨100054329985287954570547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 533623093254869091042917 100054329985287954570547)
                  ·
                    rfl

theorem cell21_438424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_438424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_438424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_438424 prefixEnd_438424 := by exact prefixLift 438424
  have htrace : WordTrace (prefixWord ++ tailWord_438424) baseStart_438424 baseEnd_438424 := by
    simpa [prefixWord, tailWord_438424, baseEnd_438424] using wordTrace_append hprefix tailTrace_438424
  have hstable : (prefixWord ++ tailWord_438424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438424).length < 2 ^ (prefixWord ++ tailWord_438424).sum := by decide
  have hdescent : baseEnd_438424 < baseStart_438424 := by decide
  rcases family_descends (prefixWord ++ tailWord_438424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438486 : List Nat := [5, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_438486 : Nat := 118140960795 + 438486 * 2 ^ 59
def prefixEnd_438486 : Nat := 4983230072969 + 3 ^ 40 * 438486 * 2
def baseEnd_438486 : Nat := 100068479229989624537087

theorem tailTrace_438486 : CollatzResearch.WordTrace tailWord_438486 prefixEnd_438486 100068479229989624537087 := by
  unfold tailWord_438486
  simp only [CollatzResearch.WordTrace]
  refine ⟨999556143090474018238457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10661932192965056194543541 999556143090474018238457)
  ·
    refine ⟨749667107317855513678843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 999556143090474018238457 749667107317855513678843)
    ·
      refine ⟨1124500660976783270518265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 749667107317855513678843 1124500660976783270518265)
      ·
        refine ⟨843375495732587452888699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1124500660976783270518265 843375495732587452888699)
        ·
          refine ⟨1265063243598881179333049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843375495732587452888699 1265063243598881179333049)
          ·
            refine ⟨948797432699160884499787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1265063243598881179333049 948797432699160884499787)
            ·
              refine ⟨1423196149048741326749681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948797432699160884499787 1423196149048741326749681)
              ·
                refine ⟨1067397111786555995062261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1423196149048741326749681 1067397111786555995062261)
                ·
                  refine ⟨100068479229989624537087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1067397111786555995062261 100068479229989624537087)
                  ·
                    rfl

theorem cell21_438486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_438486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_438486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_438486 prefixEnd_438486 := by exact prefixLift 438486
  have htrace : WordTrace (prefixWord ++ tailWord_438486) baseStart_438486 baseEnd_438486 := by
    simpa [prefixWord, tailWord_438486, baseEnd_438486] using wordTrace_append hprefix tailTrace_438486
  have hstable : (prefixWord ++ tailWord_438486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438486).length < 2 ^ (prefixWord ++ tailWord_438486).sum := by decide
  have hdescent : baseEnd_438486 < baseStart_438486 := by decide
  rcases family_descends (prefixWord ++ tailWord_438486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438562 : List Nat := [3, 3, 1, 1, 3, 1, 3, 3, 3]
def baseStart_438562 : Nat := 118140960795 + 438562 * 2 ^ 59
def prefixEnd_438562 : Nat := 4983230072969 + 3 ^ 40 * 438562 * 2
def baseEnd_438562 : Nat := 100085823465430381270265

theorem tailTrace_438562 : CollatzResearch.WordTrace tailWord_438562 prefixEnd_438562 100085823465430381270265 := by
  unfold tailWord_438562
  simp only [CollatzResearch.WordTrace]
  refine ⟨3998917559293062317895485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10663780158114832847721293 3998917559293062317895485)
  ·
    refine ⟨1499594084734898369210807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3998917559293062317895485 1499594084734898369210807)
    ·
      refine ⟨2249391127102347553816211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1499594084734898369210807 2249391127102347553816211)
      ·
        refine ⟨3374086690653521330724317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2249391127102347553816211 3374086690653521330724317)
        ·
          refine ⟨1265282508995070499021619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3374086690653521330724317 1265282508995070499021619)
          ·
            refine ⟨1897923763492605748532429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265282508995070499021619 1897923763492605748532429)
            ·
              refine ⟨711721411309727155699661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1897923763492605748532429 711721411309727155699661)
              ·
                refine ⟨266895529241147683387373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 711721411309727155699661 266895529241147683387373)
                ·
                  refine ⟨100085823465430381270265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266895529241147683387373 100085823465430381270265)
                  ·
                    rfl

theorem cell21_438562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_438562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_438562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_438562 prefixEnd_438562 := by exact prefixLift 438562
  have htrace : WordTrace (prefixWord ++ tailWord_438562) baseStart_438562 baseEnd_438562 := by
    simpa [prefixWord, tailWord_438562, baseEnd_438562] using wordTrace_append hprefix tailTrace_438562
  have hstable : (prefixWord ++ tailWord_438562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438562).length < 2 ^ (prefixWord ++ tailWord_438562).sum := by decide
  have hdescent : baseEnd_438562 < baseStart_438562 := by decide
  rcases family_descends (prefixWord ++ tailWord_438562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438590 : List Nat := [4, 2, 1, 2, 1, 3, 2, 6]
def baseStart_438590 : Nat := 118140960795 + 438590 * 2 ^ 59
def prefixEnd_438590 : Nat := 4983230072969 + 3 ^ 40 * 438590 * 2
def baseEnd_438590 : Nat := 33364071148969518267847

theorem tailTrace_438590 : CollatzResearch.WordTrace tailWord_438590 prefixEnd_438590 33364071148969518267847 := by
  unfold tailWord_438590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1999586435133851256700153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10664460987380540035734149 1999586435133851256700153)
  ·
    refine ⟨1499689826350388442525115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1999586435133851256700153 1499689826350388442525115)
    ·
      refine ⟨2249534739525582663787673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1499689826350388442525115 2249534739525582663787673)
      ·
        refine ⟨1687151054644186997840755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2249534739525582663787673 1687151054644186997840755)
        ·
          refine ⟨2530726581966280496761133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1687151054644186997840755 2530726581966280496761133)
          ·
            refine ⟨949022468237355186285425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2530726581966280496761133 949022468237355186285425)
            ·
              refine ⟨711766851178016389714069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 949022468237355186285425 711766851178016389714069)
              ·
                refine ⟨33364071148969518267847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 711766851178016389714069 33364071148969518267847)
                ·
                  rfl

theorem cell21_438590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_438590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_438590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_438590 prefixEnd_438590 := by exact prefixLift 438590
  have htrace : WordTrace (prefixWord ++ tailWord_438590) baseStart_438590 baseEnd_438590 := by
    simpa [prefixWord, tailWord_438590, baseEnd_438590] using wordTrace_append hprefix tailTrace_438590
  have hstable : (prefixWord ++ tailWord_438590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438590).length < 2 ^ (prefixWord ++ tailWord_438590).sum := by decide
  have hdescent : baseEnd_438590 < baseStart_438590 := by decide
  rcases family_descends (prefixWord ++ tailWord_438590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438804 : List Nat := [2, 4, 3, 1, 1, 1, 1, 4, 4]
def baseStart_438804 : Nat := 118140960795 + 438804 * 2 ^ 59
def prefixEnd_438804 : Nat := 4983230072969 + 3 ^ 40 * 438804 * 2
def baseEnd_438804 : Nat := 100141051162491738236437

theorem tailTrace_438804 : CollatzResearch.WordTrace tailWord_438804 prefixEnd_438804 100141051162491738236437 := by
  unfold tailWord_438804
  simp only [CollatzResearch.WordTrace]
  refine ⟨8002248351147762300945733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10669664468197016401260977 8002248351147762300945733)
  ·
    refine ⟨1500421565840205431427325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8002248351147762300945733 1500421565840205431427325)
    ·
      refine ⟨562658087190077036785247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1500421565840205431427325 562658087190077036785247)
      ·
        refine ⟨843987130785115555177871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562658087190077036785247 843987130785115555177871)
        ·
          refine ⟨1265980696177673332766807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843987130785115555177871 1265980696177673332766807)
          ·
            refine ⟨1898971044266509999150211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265980696177673332766807 1898971044266509999150211)
            ·
              refine ⟨2848456566399764998725317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1898971044266509999150211 2848456566399764998725317)
              ·
                refine ⟨534085606199955937260997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2848456566399764998725317 534085606199955937260997)
                ·
                  refine ⟨100141051162491738236437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 534085606199955937260997 100141051162491738236437)
                  ·
                    rfl

theorem cell21_438804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_438804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_438804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_438804 prefixEnd_438804 := by exact prefixLift 438804
  have htrace : WordTrace (prefixWord ++ tailWord_438804) baseStart_438804 baseEnd_438804 := by
    simpa [prefixWord, tailWord_438804, baseEnd_438804] using wordTrace_append hprefix tailTrace_438804
  have hstable : (prefixWord ++ tailWord_438804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438804).length < 2 ^ (prefixWord ++ tailWord_438804).sum := by decide
  have hdescent : baseEnd_438804 < baseStart_438804 := by decide
  rcases family_descends (prefixWord ++ tailWord_438804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438815 : List Nat := [1, 1, 2, 4, 1, 1, 1, 5, 5]
def baseStart_438815 : Nat := 118140960795 + 438815 * 2 ^ 59
def prefixEnd_438815 : Nat := 4983230072969 + 3 ^ 40 * 438815 * 2
def baseEnd_438815 : Nat := 100143561512358163553081

theorem tailTrace_438815 : CollatzResearch.WordTrace tailWord_438815 prefixEnd_438815 100143561512358163553081 := by
  unfold tailWord_438815
  simp only [CollatzResearch.WordTrace]
  refine ⟨16004897905255673480541899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10669931936837115653694599 16004897905255673480541899)
  ·
    refine ⟨24007346857883510220812849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16004897905255673480541899 24007346857883510220812849)
    ·
      refine ⟨18005510143412632665609637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24007346857883510220812849 18005510143412632665609637)
      ·
        refine ⟨3376033151889868624801807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18005510143412632665609637 3376033151889868624801807)
        ·
          refine ⟨5064049727834802937202711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3376033151889868624801807 5064049727834802937202711)
          ·
            refine ⟨7596074591752204405804067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5064049727834802937202711 7596074591752204405804067)
            ·
              refine ⟨11394111887628306608706101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7596074591752204405804067 11394111887628306608706101)
              ·
                refine ⟨1068197989465153744566197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11394111887628306608706101 1068197989465153744566197)
                ·
                  refine ⟨100143561512358163553081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1068197989465153744566197 100143561512358163553081)
                  ·
                    rfl

theorem cell21_438815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 5].length) (baseStart_438815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_438815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_438815 prefixEnd_438815 := by exact prefixLift 438815
  have htrace : WordTrace (prefixWord ++ tailWord_438815) baseStart_438815 baseEnd_438815 := by
    simpa [prefixWord, tailWord_438815, baseEnd_438815] using wordTrace_append hprefix tailTrace_438815
  have hstable : (prefixWord ++ tailWord_438815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438815).length < 2 ^ (prefixWord ++ tailWord_438815).sum := by decide
  have hdescent : baseEnd_438815 < baseStart_438815 := by decide
  rcases family_descends (prefixWord ++ tailWord_438815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438849 : List Nat := [1, 2, 5, 1, 1, 2, 1, 5, 3]
def baseStart_438849 : Nat := 118140960795 + 438849 * 2 ^ 59
def prefixEnd_438849 : Nat := 4983230072969 + 3 ^ 40 * 438849 * 2
def baseEnd_438849 : Nat := 100151320775581659986345

theorem tailTrace_438849 : CollatzResearch.WordTrace tailWord_438849 prefixEnd_438849 100151320775581659986345 := by
  unfold tailWord_438849
  simp only [CollatzResearch.WordTrace]
  refine ⟨16006137987132497287279601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10670758658088331524853067 16006137987132497287279601)
  ·
    refine ⟨12004603490349372965459701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16006137987132497287279601 12004603490349372965459701)
    ·
      refine ⟨1125431577220253715511847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12004603490349372965459701 1125431577220253715511847)
      ·
        refine ⟨1688147365830380573267771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1125431577220253715511847 1688147365830380573267771)
        ·
          refine ⟨2532221048745570859901657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1688147365830380573267771 2532221048745570859901657)
          ·
            refine ⟨1899165786559178144926243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2532221048745570859901657 1899165786559178144926243)
            ·
              refine ⟨2848748679838767217389365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899165786559178144926243 2848748679838767217389365)
              ·
                refine ⟨267070188734884426630253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2848748679838767217389365 267070188734884426630253)
                ·
                  refine ⟨100151320775581659986345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267070188734884426630253 100151320775581659986345)
                  ·
                    rfl

theorem cell21_438849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 3].length) (baseStart_438849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_438849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_438849 prefixEnd_438849 := by exact prefixLift 438849
  have htrace : WordTrace (prefixWord ++ tailWord_438849) baseStart_438849 baseEnd_438849 := by
    simpa [prefixWord, tailWord_438849, baseEnd_438849] using wordTrace_append hprefix tailTrace_438849
  have hstable : (prefixWord ++ tailWord_438849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438849).length < 2 ^ (prefixWord ++ tailWord_438849).sum := by decide
  have hdescent : baseEnd_438849 < baseStart_438849 := by decide
  rcases family_descends (prefixWord ++ tailWord_438849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438860 : List Nat := [2, 2, 1, 3, 1, 2, 10]
def baseStart_438860 : Nat := 118140960795 + 438860 * 2 ^ 59
def prefixEnd_438860 : Nat := 4983230072969 + 3 ^ 40 * 438860 * 2
def baseEnd_438860 : Nat := 11128203458383120589221

theorem tailTrace_438860 : CollatzResearch.WordTrace tailWord_438860 prefixEnd_438860 11128203458383120589221 := by
  unfold tailWord_438860
  simp only [CollatzResearch.WordTrace]
  refine ⟨8003269595046323082965017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10671026126728430777286689 8003269595046323082965017)
  ·
    refine ⟨6002452196284742312223763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8003269595046323082965017 6002452196284742312223763)
    ·
      refine ⟨9003678294427113468335645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6002452196284742312223763 9003678294427113468335645)
      ·
        refine ⟨3376379360410167550625867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9003678294427113468335645 3376379360410167550625867)
        ·
          refine ⟨5064569040615251325938801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3376379360410167550625867 5064569040615251325938801)
          ·
            refine ⟨3798426780461438494454101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5064569040615251325938801 3798426780461438494454101)
            ·
              refine ⟨11128203458383120589221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3798426780461438494454101 11128203458383120589221)
              ·
                rfl

theorem cell21_438860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 10].length) (baseStart_438860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_438860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_438860 prefixEnd_438860 := by exact prefixLift 438860
  have htrace : WordTrace (prefixWord ++ tailWord_438860) baseStart_438860 baseEnd_438860 := by
    simpa [prefixWord, tailWord_438860, baseEnd_438860] using wordTrace_append hprefix tailTrace_438860
  have hstable : (prefixWord ++ tailWord_438860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438860).length < 2 ^ (prefixWord ++ tailWord_438860).sum := by decide
  have hdescent : baseEnd_438860 < baseStart_438860 := by decide
  rcases family_descends (prefixWord ++ tailWord_438860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438894 : List Nat := [4, 1, 2, 2, 2, 1, 4, 5]
def baseStart_438894 : Nat := 118140960795 + 438894 * 2 ^ 59
def prefixEnd_438894 : Nat := 4983230072969 + 3 ^ 40 * 438894 * 2
def baseEnd_438894 : Nat := 33387196796223860578751

theorem tailTrace_438894 : CollatzResearch.WordTrace tailWord_438894 prefixEnd_438894 33387196796223860578751 := by
  unfold tailWord_438894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000972408996183746583467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10671852847979646648445157 2000972408996183746583467)
  ·
    refine ⟨3001458613494275619875201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2000972408996183746583467 3001458613494275619875201)
    ·
      refine ⟨2251093960120706714906401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3001458613494275619875201 2251093960120706714906401)
      ·
        refine ⟨1688320470090530036179801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2251093960120706714906401 1688320470090530036179801)
        ·
          refine ⟨1266240352567897527134851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1688320470090530036179801 1266240352567897527134851)
          ·
            refine ⟨1899360528851846290702277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266240352567897527134851 1899360528851846290702277)
            ·
              refine ⟨356130099159721179506677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1899360528851846290702277 356130099159721179506677)
              ·
                refine ⟨33387196796223860578751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 356130099159721179506677 33387196796223860578751)
                ·
                  rfl

theorem cell21_438894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_438894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_438894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_438894 prefixEnd_438894 := by exact prefixLift 438894
  have htrace : WordTrace (prefixWord ++ tailWord_438894) baseStart_438894 baseEnd_438894 := by
    simpa [prefixWord, tailWord_438894, baseEnd_438894] using wordTrace_append hprefix tailTrace_438894
  have hstable : (prefixWord ++ tailWord_438894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438894).length < 2 ^ (prefixWord ++ tailWord_438894).sum := by decide
  have hdescent : baseEnd_438894 < baseStart_438894 := by decide
  rcases family_descends (prefixWord ++ tailWord_438894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439063 : List Nat := [1, 1, 3, 4, 4, 1, 2, 5]
def baseStart_439063 : Nat := 118140960795 + 439063 * 2 ^ 59
def prefixEnd_439063 : Nat := 4983230072969 + 3 ^ 40 * 439063 * 2
def baseEnd_439063 : Nat := 33400052830388281139747

theorem tailTrace_439063 : CollatzResearch.WordTrace tailWord_439063 prefixEnd_439063 33400052830388281139747 := by
  unfold tailWord_439063
  simp only [CollatzResearch.WordTrace]
  refine ⟨16013943208357211835569843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10675962138904807890379895 16013943208357211835569843)
  ·
    refine ⟨24020914812535817753354765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16013943208357211835569843 24020914812535817753354765)
    ·
      refine ⟨9007843054700931657508037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24020914812535817753354765 9007843054700931657508037)
      ·
        refine ⟨1688970572756424685782757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9007843054700931657508037 1688970572756424685782757)
        ·
          refine ⟨316681982391829628584267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1688970572756424685782757 316681982391829628584267)
          ·
            refine ⟨475022973587744442876401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316681982391829628584267 475022973587744442876401)
            ·
              refine ⟨356267230190808332157301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475022973587744442876401 356267230190808332157301)
              ·
                refine ⟨33400052830388281139747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 356267230190808332157301 33400052830388281139747)
                ·
                  rfl

theorem cell21_439063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 5].length) (baseStart_439063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439063 prefixEnd_439063 := by exact prefixLift 439063
  have htrace : WordTrace (prefixWord ++ tailWord_439063) baseStart_439063 baseEnd_439063 := by
    simpa [prefixWord, tailWord_439063, baseEnd_439063] using wordTrace_append hprefix tailTrace_439063
  have hstable : (prefixWord ++ tailWord_439063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439063).length < 2 ^ (prefixWord ++ tailWord_439063).sum := by decide
  have hdescent : baseEnd_439063 < baseStart_439063 := by decide
  rcases family_descends (prefixWord ++ tailWord_439063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439074 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 6]
def baseStart_439074 : Nat := 118140960795 + 439074 * 2 ^ 59
def prefixEnd_439074 : Nat := 4983230072969 + 3 ^ 40 * 439074 * 2
def baseEnd_439074 : Nat := 100202668841031268735885

theorem tailTrace_439074 : CollatzResearch.WordTrace tailWord_439074 prefixEnd_439074 100202668841031268735885 := by
  unfold tailWord_439074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4003586102829340178555069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10676229607544907142813517 4003586102829340178555069)
  ·
    refine ⟨1501344788561002566958151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4003586102829340178555069 1501344788561002566958151)
    ·
      refine ⟨2252017182841503850437227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1501344788561002566958151 2252017182841503850437227)
      ·
        refine ⟨3378025774262255775655841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2252017182841503850437227 3378025774262255775655841)
        ·
          refine ⟨2533519330696691831741881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3378025774262255775655841 2533519330696691831741881)
          ·
            refine ⟨1900139498022518873806411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2533519330696691831741881 1900139498022518873806411)
            ·
              refine ⟨2850209247033778310709617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900139498022518873806411 2850209247033778310709617)
              ·
                refine ⟨2137656935275333733032213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850209247033778310709617 2137656935275333733032213)
                ·
                  refine ⟨100202668841031268735885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2137656935275333733032213 100202668841031268735885)
                  ·
                    rfl

theorem cell21_439074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_439074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439074 prefixEnd_439074 := by exact prefixLift 439074
  have htrace : WordTrace (prefixWord ++ tailWord_439074) baseStart_439074 baseEnd_439074 := by
    simpa [prefixWord, tailWord_439074, baseEnd_439074] using wordTrace_append hprefix tailTrace_439074
  have hstable : (prefixWord ++ tailWord_439074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439074).length < 2 ^ (prefixWord ++ tailWord_439074).sum := by decide
  have hdescent : baseEnd_439074 < baseStart_439074 := by decide
  rcases family_descends (prefixWord ++ tailWord_439074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439094 : List Nat := [5, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_439094 : Nat := 118140960795 + 439094 * 2 ^ 59
def prefixEnd_439094 : Nat := 4983230072969 + 3 ^ 40 * 439094 * 2
def baseEnd_439094 : Nat := 100207233113515678402511

theorem tailTrace_439094 : CollatzResearch.WordTrace tailWord_439094 prefixEnd_439094 100207233113515678402511 := by
  unfold tailWord_439094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1000942116952806508121771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10676715914163269419965557 1000942116952806508121771)
  ·
    refine ⟨1501413175429209762182657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1000942116952806508121771 1501413175429209762182657)
    ·
      refine ⟨1126059881571907321636993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1501413175429209762182657 1126059881571907321636993)
      ·
        refine ⟨844544911178930491227745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1126059881571907321636993 844544911178930491227745)
        ·
          refine ⟨633408683384197868420809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 844544911178930491227745 633408683384197868420809)
          ·
            refine ⟨475056512538148401315607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 633408683384197868420809 475056512538148401315607)
            ·
              refine ⟨712584768807222601973411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475056512538148401315607 712584768807222601973411)
              ·
                refine ⟨1068877153210833902960117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712584768807222601973411 1068877153210833902960117)
                ·
                  refine ⟨100207233113515678402511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1068877153210833902960117 100207233113515678402511)
                  ·
                    rfl

theorem cell21_439094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_439094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439094 prefixEnd_439094 := by exact prefixLift 439094
  have htrace : WordTrace (prefixWord ++ tailWord_439094) baseStart_439094 baseEnd_439094 := by
    simpa [prefixWord, tailWord_439094, baseEnd_439094] using wordTrace_append hprefix tailTrace_439094
  have hstable : (prefixWord ++ tailWord_439094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439094).length < 2 ^ (prefixWord ++ tailWord_439094).sum := by decide
  have hdescent : baseEnd_439094 < baseStart_439094 := by decide
  rcases family_descends (prefixWord ++ tailWord_439094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439136 : List Nat := [2, 1, 1, 3, 3, 1, 2, 5, 3]
def baseStart_439136 : Nat := 118140960795 + 439136 * 2 ^ 59
def prefixEnd_439136 : Nat := 4983230072969 + 3 ^ 40 * 439136 * 2
def baseEnd_439136 : Nat := 100216818085732938702425

theorem tailTrace_439136 : CollatzResearch.WordTrace tailWord_439136 prefixEnd_439136 100216818085732938702425 := by
  unfold tailWord_439136
  simp only [CollatzResearch.WordTrace]
  refine ⟨8008302868546372651488631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10677737158061830201984841 8008302868546372651488631)
  ·
    refine ⟨12012454302819558977232947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8008302868546372651488631 12012454302819558977232947)
    ·
      refine ⟨18018681454229338465849421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12012454302819558977232947 18018681454229338465849421)
      ·
        refine ⟨6757005545336001924693533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18018681454229338465849421 6757005545336001924693533)
        ·
          refine ⟨2533877079501000721760075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6757005545336001924693533 2533877079501000721760075)
          ·
            refine ⟨3800815619251501082640113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2533877079501000721760075 3800815619251501082640113)
            ·
              refine ⟨2850611714438625811980085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3800815619251501082640113 2850611714438625811980085)
              ·
                refine ⟨267244848228621169873133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2850611714438625811980085 267244848228621169873133)
                ·
                  refine ⟨100216818085732938702425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267244848228621169873133 100216818085732938702425)
                  ·
                    rfl

theorem cell21_439136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 3].length) (baseStart_439136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439136 prefixEnd_439136 := by exact prefixLift 439136
  have htrace : WordTrace (prefixWord ++ tailWord_439136) baseStart_439136 baseEnd_439136 := by
    simpa [prefixWord, tailWord_439136, baseEnd_439136] using wordTrace_append hprefix tailTrace_439136
  have hstable : (prefixWord ++ tailWord_439136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439136).length < 2 ^ (prefixWord ++ tailWord_439136).sum := by decide
  have hdescent : baseEnd_439136 < baseStart_439136 := by decide
  rcases family_descends (prefixWord ++ tailWord_439136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439153 : List Nat := [1, 2, 2, 2, 1, 4, 4, 2, 3]
def baseStart_439153 : Nat := 118140960795 + 439153 * 2 ^ 59
def prefixEnd_439153 : Nat := 4983230072969 + 3 ^ 40 * 439153 * 2
def baseEnd_439153 : Nat := 100220697717344686919057

theorem tailTrace_439153 : CollatzResearch.WordTrace tailWord_439153 prefixEnd_439153 100220697717344686919057 := by
  unfold tailWord_439153
  simp only [CollatzResearch.WordTrace]
  refine ⟨16017225778031157206346113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10678150518687438137564075 16017225778031157206346113)
  ·
    refine ⟨12012919333523367904759585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16017225778031157206346113 12012919333523367904759585)
    ·
      refine ⟨9009689500142525928569689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12012919333523367904759585 9009689500142525928569689)
      ·
        refine ⟨6757267125106894446427267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9009689500142525928569689 6757267125106894446427267)
        ·
          refine ⟨10135900687660341669640901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6757267125106894446427267 10135900687660341669640901)
          ·
            refine ⟨1900481378936314063057669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10135900687660341669640901 1900481378936314063057669)
            ·
              refine ⟨356340258550558886823313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1900481378936314063057669 356340258550558886823313)
              ·
                refine ⟨267255193912919165117485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356340258550558886823313 267255193912919165117485)
                ·
                  refine ⟨100220697717344686919057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267255193912919165117485 100220697717344686919057)
                  ·
                    rfl

theorem cell21_439153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 3].length) (baseStart_439153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439153 prefixEnd_439153 := by exact prefixLift 439153
  have htrace : WordTrace (prefixWord ++ tailWord_439153) baseStart_439153 baseEnd_439153 := by
    simpa [prefixWord, tailWord_439153, baseEnd_439153] using wordTrace_append hprefix tailTrace_439153
  have hstable : (prefixWord ++ tailWord_439153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439153).length < 2 ^ (prefixWord ++ tailWord_439153).sum := by decide
  have hdescent : baseEnd_439153 < baseStart_439153 := by decide
  rcases family_descends (prefixWord ++ tailWord_439153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439170 : List Nat := [3, 4, 2, 2, 1, 1, 1, 2, 5]
def baseStart_439170 : Nat := 118140960795 + 439170 * 2 ^ 59
def prefixEnd_439170 : Nat := 4983230072969 + 3 ^ 40 * 439170 * 2
def baseEnd_439170 : Nat := 100224577348956435135689

theorem tailTrace_439170 : CollatzResearch.WordTrace tailWord_439170 prefixEnd_439170 100224577348956435135689 := by
  unfold tailWord_439170
  simp only [CollatzResearch.WordTrace]
  refine ⟨4004461454742392277428741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10678563879313046073143309 4004461454742392277428741)
  ·
    refine ⟨750836522764198552017889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4004461454742392277428741 750836522764198552017889)
    ·
      refine ⟨563127392073148914013417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 750836522764198552017889 563127392073148914013417)
      ·
        refine ⟨422345544054861685510063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 563127392073148914013417 422345544054861685510063)
        ·
          refine ⟨633518316082292528265095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422345544054861685510063 633518316082292528265095)
          ·
            refine ⟨950277474123438792397643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633518316082292528265095 950277474123438792397643)
            ·
              refine ⟨1425416211185158188596465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950277474123438792397643 1425416211185158188596465)
              ·
                refine ⟨1069062158388868641447349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1425416211185158188596465 1069062158388868641447349)
                ·
                  refine ⟨100224577348956435135689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1069062158388868641447349 100224577348956435135689)
                  ·
                    rfl

theorem cell21_439170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_439170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439170 prefixEnd_439170 := by exact prefixLift 439170
  have htrace : WordTrace (prefixWord ++ tailWord_439170) baseStart_439170 baseEnd_439170 := by
    simpa [prefixWord, tailWord_439170, baseEnd_439170] using wordTrace_append hprefix tailTrace_439170
  have hstable : (prefixWord ++ tailWord_439170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439170).length < 2 ^ (prefixWord ++ tailWord_439170).sum := by decide
  have hdescent : baseEnd_439170 < baseStart_439170 := by decide
  rcases family_descends (prefixWord ++ tailWord_439170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439209 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 6]
def baseStart_439209 : Nat := 118140960795 + 439209 * 2 ^ 59
def prefixEnd_439209 : Nat := 4983230072969 + 3 ^ 40 * 439209 * 2
def baseEnd_439209 : Nat := 100233477680301033985609

theorem tailTrace_439209 : CollatzResearch.WordTrace tailWord_439209 prefixEnd_439209 100233477680301033985609 := by
  unfold tailWord_439209
  simp only [CollatzResearch.WordTrace]
  refine ⟨16019268265828278770384681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10679512177218852513589787 16019268265828278770384681)
  ·
    refine ⟨12014451199371209077788511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16019268265828278770384681 12014451199371209077788511)
    ·
      refine ⟨18021676799056813616682767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12014451199371209077788511 18021676799056813616682767)
      ·
        refine ⟨27032515198585220425024151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18021676799056813616682767 27032515198585220425024151)
        ·
          refine ⟨40548772797877830637536227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27032515198585220425024151 40548772797877830637536227)
          ·
            refine ⟨60823159196816745956304341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40548772797877830637536227 60823159196816745956304341)
            ·
              refine ⟨1425542793675392483350883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 60823159196816745956304341 1425542793675392483350883)
              ·
                refine ⟨2138314190513088725026325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1425542793675392483350883 2138314190513088725026325)
                ·
                  refine ⟨100233477680301033985609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2138314190513088725026325 100233477680301033985609)
                  ·
                    rfl

theorem cell21_439209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_439209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439209 prefixEnd_439209 := by exact prefixLift 439209
  have htrace : WordTrace (prefixWord ++ tailWord_439209) baseStart_439209 baseEnd_439209 := by
    simpa [prefixWord, tailWord_439209, baseEnd_439209] using wordTrace_append hprefix tailTrace_439209
  have hstable : (prefixWord ++ tailWord_439209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439209).length < 2 ^ (prefixWord ++ tailWord_439209).sum := by decide
  have hdescent : baseEnd_439209 < baseStart_439209 := by decide
  rcases family_descends (prefixWord ++ tailWord_439209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439238 : List Nat := [6, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_439238 : Nat := 118140960795 + 439238 * 2 ^ 59
def prefixEnd_439238 : Nat := 4983230072969 + 3 ^ 40 * 439238 * 2
def baseEnd_439238 : Nat := 100240095875403428002217

theorem tailTrace_439238 : CollatzResearch.WordTrace tailWord_439238 prefixEnd_439238 100240095875403428002217 := by
  unfold tailWord_439238
  simp only [CollatzResearch.WordTrace]
  refine ⟨500635186960100522599699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10680217321815477815460245 500635186960100522599699)
  ·
    refine ⟨750952780440150783899549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 500635186960100522599699 750952780440150783899549)
    ·
      refine ⟨281607292665056543962331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 750952780440150783899549 281607292665056543962331)
      ·
        refine ⟨422410938997584815943497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281607292665056543962331 422410938997584815943497)
        ·
          refine ⟨316808204248188611957623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422410938997584815943497 316808204248188611957623)
          ·
            refine ⟨475212306372282917936435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316808204248188611957623 475212306372282917936435)
            ·
              refine ⟨712818459558424376904653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475212306372282917936435 712818459558424376904653)
              ·
                refine ⟨267306922334409141339245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 712818459558424376904653 267306922334409141339245)
                ·
                  refine ⟨100240095875403428002217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267306922334409141339245 100240095875403428002217)
                  ·
                    rfl

theorem cell21_439238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_439238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439238 prefixEnd_439238 := by exact prefixLift 439238
  have htrace : WordTrace (prefixWord ++ tailWord_439238) baseStart_439238 baseEnd_439238 := by
    simpa [prefixWord, tailWord_439238, baseEnd_439238] using wordTrace_append hprefix tailTrace_439238
  have hstable : (prefixWord ++ tailWord_439238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439238).length < 2 ^ (prefixWord ++ tailWord_439238).sum := by decide
  have hdescent : baseEnd_439238 < baseStart_439238 := by decide
  rcases family_descends (prefixWord ++ tailWord_439238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439316 : List Nat := [2, 4, 3, 12]
def baseStart_439316 : Nat := 118140960795 + 439316 * 2 ^ 59
def prefixEnd_439316 : Nat := 4983230072969 + 3 ^ 40 * 439316 * 2
def baseEnd_439316 : Nat := 412583936370751546099

theorem tailTrace_439316 : CollatzResearch.WordTrace tailWord_439316 prefixEnd_439316 412583936370751546099 := by
  unfold tailWord_439316
  simp only [CollatzResearch.WordTrace]
  refine ⟨8011585438220318022264901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10682113917627090696353201 8011585438220318022264901)
  ·
    refine ⟨1502172269666309629174669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8011585438220318022264901 1502172269666309629174669)
    ·
      refine ⟨563314601124866110940501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1502172269666309629174669 563314601124866110940501)
      ·
        refine ⟨412583936370751546099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 563314601124866110940501 412583936370751546099)
        ·
          rfl

theorem cell21_439316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 12].length) (baseStart_439316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439316 prefixEnd_439316 := by exact prefixLift 439316
  have htrace : WordTrace (prefixWord ++ tailWord_439316) baseStart_439316 baseEnd_439316 := by
    simpa [prefixWord, tailWord_439316, baseEnd_439316] using wordTrace_append hprefix tailTrace_439316
  have hstable : (prefixWord ++ tailWord_439316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439316).length < 2 ^ (prefixWord ++ tailWord_439316).sum := by decide
  have hdescent : baseEnd_439316 < baseStart_439316 := by decide
  rcases family_descends (prefixWord ++ tailWord_439316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439319 : List Nat := [1, 1, 3, 5, 1, 2, 2, 2, 4]
def baseStart_439319 : Nat := 118140960795 + 439319 * 2 ^ 59
def prefixEnd_439319 : Nat := 4983230072969 + 3 ^ 40 * 439319 * 2
def baseEnd_439319 : Nat := 100258581178965287152051

theorem tailTrace_439319 : CollatzResearch.WordTrace tailWord_439319 prefixEnd_439319 100258581178965287152051 := by
  unfold tailWord_439319
  simp only [CollatzResearch.WordTrace]
  refine ⟨16023280295429767556889011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10682186863619845037926007 16023280295429767556889011)
  ·
    refine ⟨24034920443144651335333517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16023280295429767556889011 24034920443144651335333517)
    ·
      refine ⟨9013095166179244250750069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24034920443144651335333517 9013095166179244250750069)
      ·
        refine ⟨844977671829304148507819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9013095166179244250750069 844977671829304148507819)
        ·
          refine ⟨1267466507743956222761729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844977671829304148507819 1267466507743956222761729)
          ·
            refine ⟨950599880807967167071297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1267466507743956222761729 950599880807967167071297)
            ·
              refine ⟨712949910605975375303473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 950599880807967167071297 712949910605975375303473)
              ·
                refine ⟨534712432954481531477605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712949910605975375303473 534712432954481531477605)
                ·
                  refine ⟨100258581178965287152051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 534712432954481531477605 100258581178965287152051)
                  ·
                    rfl

theorem cell21_439319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 4].length) (baseStart_439319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439319 prefixEnd_439319 := by exact prefixLift 439319
  have htrace : WordTrace (prefixWord ++ tailWord_439319) baseStart_439319 baseEnd_439319 := by
    simpa [prefixWord, tailWord_439319, baseEnd_439319] using wordTrace_append hprefix tailTrace_439319
  have hstable : (prefixWord ++ tailWord_439319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439319).length < 2 ^ (prefixWord ++ tailWord_439319).sum := by decide
  have hdescent : baseEnd_439319 < baseStart_439319 := by decide
  rcases family_descends (prefixWord ++ tailWord_439319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439350 : List Nat := [5, 1, 2, 1, 1, 3, 3, 5]
def baseStart_439350 : Nat := 118140960795 + 439350 * 2 ^ 59
def prefixEnd_439350 : Nat := 4983230072969 + 3 ^ 40 * 439350 * 2
def baseEnd_439350 : Nat := 33421885267105374045107

theorem tailTrace_439350 : CollatzResearch.WordTrace tailWord_439350 prefixEnd_439350 33421885267105374045107 := by
  unfold tailWord_439350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1001525684894841240704219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10682940638878306567511669 1001525684894841240704219)
  ·
    refine ⟨1502288527342261861056329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1001525684894841240704219 1502288527342261861056329)
    ·
      refine ⟨1126716395506696395792247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1502288527342261861056329 1126716395506696395792247)
      ·
        refine ⟨1690074593260044593688371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1126716395506696395792247 1690074593260044593688371)
        ·
          refine ⟨2535111889890066890532557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1690074593260044593688371 2535111889890066890532557)
          ·
            refine ⟨950666958708775083949709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2535111889890066890532557 950666958708775083949709)
            ·
              refine ⟨356500109515790656481141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 950666958708775083949709 356500109515790656481141)
              ·
                refine ⟨33421885267105374045107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 356500109515790656481141 33421885267105374045107)
                ·
                  rfl

theorem cell21_439350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_439350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439350 prefixEnd_439350 := by exact prefixLift 439350
  have htrace : WordTrace (prefixWord ++ tailWord_439350) baseStart_439350 baseEnd_439350 := by
    simpa [prefixWord, tailWord_439350, baseEnd_439350] using wordTrace_append hprefix tailTrace_439350
  have hstable : (prefixWord ++ tailWord_439350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439350).length < 2 ^ (prefixWord ++ tailWord_439350).sum := by decide
  have hdescent : baseEnd_439350 < baseStart_439350 := by decide
  rcases family_descends (prefixWord ++ tailWord_439350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439378 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 6]
def baseStart_439378 : Nat := 118140960795 + 439378 * 2 ^ 59
def prefixEnd_439378 : Nat := 4983230072969 + 3 ^ 40 * 439378 * 2
def baseEnd_439378 : Nat := 100272045782794295668597

theorem tailTrace_439378 : CollatzResearch.WordTrace tailWord_439378 prefixEnd_439378 100272045782794295668597 := by
  unfold tailWord_439378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4006358050554005158321697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10683621468144013755524525 4006358050554005158321697)
  ·
    refine ⟨3004768537915503868741273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4006358050554005158321697 3004768537915503868741273)
    ·
      refine ⟨2253576403436627901555955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3004768537915503868741273 2253576403436627901555955)
      ·
        refine ⟨3380364605154941852333933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2253576403436627901555955 3380364605154941852333933)
        ·
          refine ⟨1267636726933103194625225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3380364605154941852333933 1267636726933103194625225)
          ·
            refine ⟨950727545199827395968919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1267636726933103194625225 950727545199827395968919)
            ·
              refine ⟨1426091317799741093953379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950727545199827395968919 1426091317799741093953379)
              ·
                refine ⟨2139136976699611640930069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1426091317799741093953379 2139136976699611640930069)
                ·
                  refine ⟨100272045782794295668597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2139136976699611640930069 100272045782794295668597)
                  ·
                    rfl

theorem cell21_439378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_439378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439378 prefixEnd_439378 := by exact prefixLift 439378
  have htrace : WordTrace (prefixWord ++ tailWord_439378) baseStart_439378 baseEnd_439378 := by
    simpa [prefixWord, tailWord_439378, baseEnd_439378] using wordTrace_append hprefix tailTrace_439378
  have hstable : (prefixWord ++ tailWord_439378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439378).length < 2 ^ (prefixWord ++ tailWord_439378).sum := by decide
  have hdescent : baseEnd_439378 < baseStart_439378 := by decide
  rcases family_descends (prefixWord ++ tailWord_439378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439502 : List Nat := [4, 1, 1, 1, 6, 1, 1, 6]
def baseStart_439502 : Nat := 118140960795 + 439502 * 2 ^ 59
def prefixEnd_439502 : Nat := 4983230072969 + 3 ^ 40 * 439502 * 2
def baseEnd_439502 : Nat := 33433448090732545200559

theorem tailTrace_439502 : CollatzResearch.WordTrace tailWord_439502 prefixEnd_439502 33433448090732545200559 := by
  unfold tailWord_439502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2003744356720848726350095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10686636569177859873867173 2003744356720848726350095)
  ·
    refine ⟨3005616535081273089525143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2003744356720848726350095 3005616535081273089525143)
    ·
      refine ⟨4508424802621909634287715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3005616535081273089525143 4508424802621909634287715)
      ·
        refine ⟨6762637203932864451431573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4508424802621909634287715 6762637203932864451431573)
        ·
          refine ⟨316998618934353021160855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6762637203932864451431573 316998618934353021160855)
          ·
            refine ⟨475497928401529531741283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316998618934353021160855 475497928401529531741283)
            ·
              refine ⟨713246892602294297611925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475497928401529531741283 713246892602294297611925)
              ·
                refine ⟨33433448090732545200559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 713246892602294297611925 33433448090732545200559)
                ·
                  rfl

theorem cell21_439502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_439502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439502 prefixEnd_439502 := by exact prefixLift 439502
  have htrace : WordTrace (prefixWord ++ tailWord_439502) baseStart_439502 baseEnd_439502 := by
    simpa [prefixWord, tailWord_439502, baseEnd_439502] using wordTrace_append hprefix tailTrace_439502
  have hstable : (prefixWord ++ tailWord_439502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439502).length < 2 ^ (prefixWord ++ tailWord_439502).sum := by decide
  have hdescent : baseEnd_439502 < baseStart_439502 := by decide
  rcases family_descends (prefixWord ++ tailWord_439502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439533 : List Nat := [1, 5, 1, 2, 2, 2, 2, 3, 3]
def baseStart_439533 : Nat := 118140960795 + 439533 * 2 ^ 59
def prefixEnd_439533 : Nat := 4983230072969 + 3 ^ 40 * 439533 * 2
def baseEnd_439533 : Nat := 100307418894548470584947

theorem tailTrace_439533 : CollatzResearch.WordTrace tailWord_439533 prefixEnd_439533 100307418894548470584947 := by
  unfold tailWord_439533
  simp only [CollatzResearch.WordTrace]
  refine ⟨16031085516654482105179253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10687390344436321403452835 16031085516654482105179253)
  ·
    refine ⟨1502914267186357697360555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16031085516654482105179253 1502914267186357697360555)
    ·
      refine ⟨2254371400779536546040833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1502914267186357697360555 2254371400779536546040833)
      ·
        refine ⟨1690778550584652409530625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2254371400779536546040833 1690778550584652409530625)
        ·
          refine ⟨1268083912938489307147969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1690778550584652409530625 1268083912938489307147969)
          ·
            refine ⟨951062934703866980360977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1268083912938489307147969 951062934703866980360977)
            ·
              refine ⟨713297201027900235270733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951062934703866980360977 713297201027900235270733)
              ·
                refine ⟨267486450385462588226525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 713297201027900235270733 267486450385462588226525)
                ·
                  refine ⟨100307418894548470584947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267486450385462588226525 100307418894548470584947)
                  ·
                    rfl

theorem cell21_439533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_439533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439533 prefixEnd_439533 := by exact prefixLift 439533
  have htrace : WordTrace (prefixWord ++ tailWord_439533) baseStart_439533 baseEnd_439533 := by
    simpa [prefixWord, tailWord_439533, baseEnd_439533] using wordTrace_append hprefix tailTrace_439533
  have hstable : (prefixWord ++ tailWord_439533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439533).length < 2 ^ (prefixWord ++ tailWord_439533).sum := by decide
  have hdescent : baseEnd_439533 < baseStart_439533 := by decide
  rcases family_descends (prefixWord ++ tailWord_439533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439589 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 6]
def baseStart_439589 : Nat := 118140960795 + 439589 * 2 ^ 59
def prefixEnd_439589 : Nat := 4983230072969 + 3 ^ 40 * 439589 * 2
def baseEnd_439589 : Nat := 100320198857504817651499

theorem tailTrace_439589 : CollatzResearch.WordTrace tailWord_439589 prefixEnd_439589 100320198857504817651499 := by
  unfold tailWord_439589
  simp only [CollatzResearch.WordTrace]
  refine ⟨16033128004451603669217821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10688752002967735779478547 16033128004451603669217821)
  ·
    refine ⟨6012423001669351375956683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16033128004451603669217821 6012423001669351375956683)
    ·
      refine ⟨9018634502504027063935025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6012423001669351375956683 9018634502504027063935025)
      ·
        refine ⟨6763975876878020297951269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9018634502504027063935025 6763975876878020297951269)
        ·
          refine ⟨1268245476914628805865863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6763975876878020297951269 1268245476914628805865863)
          ·
            refine ⟨1902368215371943208798795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268245476914628805865863 1902368215371943208798795)
            ·
              refine ⟨2853552323057914813198193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902368215371943208798795 2853552323057914813198193)
              ·
                refine ⟨2140164242293436109898645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2853552323057914813198193 2140164242293436109898645)
                ·
                  refine ⟨100320198857504817651499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2140164242293436109898645 100320198857504817651499)
                  ·
                    rfl

theorem cell21_439589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_439589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439589 prefixEnd_439589 := by exact prefixLift 439589
  have htrace : WordTrace (prefixWord ++ tailWord_439589) baseStart_439589 baseEnd_439589 := by
    simpa [prefixWord, tailWord_439589, baseEnd_439589] using wordTrace_append hprefix tailTrace_439589
  have hstable : (prefixWord ++ tailWord_439589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439589).length < 2 ^ (prefixWord ++ tailWord_439589).sum := by decide
  have hdescent : baseEnd_439589 < baseStart_439589 := by decide
  rcases family_descends (prefixWord ++ tailWord_439589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439603 : List Nat := [1, 1, 1, 2, 5, 2, 9]
def baseStart_439603 : Nat := 118140960795 + 439603 * 2 ^ 59
def prefixEnd_439603 : Nat := 4983230072969 + 3 ^ 40 * 439603 * 2
def baseEnd_439603 : Nat := 11147043760915989379793

theorem tailTrace_439603 : CollatzResearch.WordTrace tailWord_439603 prefixEnd_439603 11147043760915989379793 := by
  unfold tailWord_439603
  simp only [CollatzResearch.WordTrace]
  refine ⟨16033638626400884060227463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10689092417600589373484975 16033638626400884060227463)
  ·
    refine ⟨24050457939601326090341195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16033638626400884060227463 24050457939601326090341195)
    ·
      refine ⟨36075686909401989135511793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24050457939601326090341195 36075686909401989135511793)
      ·
        refine ⟨27056765182051491851633845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36075686909401989135511793 27056765182051491851633845)
        ·
          refine ⟨2536571735817327361090673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27056765182051491851633845 2536571735817327361090673)
          ·
            refine ⟨1902428801862995520818005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2536571735817327361090673 1902428801862995520818005)
            ·
              refine ⟨11147043760915989379793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1902428801862995520818005 11147043760915989379793)
              ·
                rfl

theorem cell21_439603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 9].length) (baseStart_439603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439603 prefixEnd_439603 := by exact prefixLift 439603
  have htrace : WordTrace (prefixWord ++ tailWord_439603) baseStart_439603 baseEnd_439603 := by
    simpa [prefixWord, tailWord_439603, baseEnd_439603] using wordTrace_append hprefix tailTrace_439603
  have hstable : (prefixWord ++ tailWord_439603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439603).length < 2 ^ (prefixWord ++ tailWord_439603).sum := by decide
  have hdescent : baseEnd_439603 < baseStart_439603 := by decide
  rcases family_descends (prefixWord ++ tailWord_439603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439609 : List Nat := [1, 2, 1, 6, 3, 1, 1, 1, 5]
def baseStart_439609 : Nat := 118140960795 + 439609 * 2 ^ 59
def prefixEnd_439609 : Nat := 4983230072969 + 3 ^ 40 * 439609 * 2
def baseEnd_439609 : Nat := 100324763129989227318125

theorem tailTrace_439609 : CollatzResearch.WordTrace tailWord_439609 prefixEnd_439609 100324763129989227318125 := by
  unfold tailWord_439609
  simp only [CollatzResearch.WordTrace]
  refine ⟨16033857464379147084945881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10689238309586098056630587 16033857464379147084945881)
  ·
    refine ⟨12025393098284360313709411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16033857464379147084945881 12025393098284360313709411)
    ·
      refine ⟨18038089647426540470564117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12025393098284360313709411 18038089647426540470564117)
      ·
        refine ⟨845535452223119084557693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18038089647426540470564117 845535452223119084557693)
        ·
          refine ⟨317075794583669656709135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 845535452223119084557693 317075794583669656709135)
          ·
            refine ⟨475613691875504485063703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317075794583669656709135 475613691875504485063703)
            ·
              refine ⟨713420537813256727595555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475613691875504485063703 713420537813256727595555)
              ·
                refine ⟨1070130806719885091393333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713420537813256727595555 1070130806719885091393333)
                ·
                  refine ⟨100324763129989227318125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1070130806719885091393333 100324763129989227318125)
                  ·
                    rfl

theorem cell21_439609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 5].length) (baseStart_439609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439609 prefixEnd_439609 := by exact prefixLift 439609
  have htrace : WordTrace (prefixWord ++ tailWord_439609) baseStart_439609 baseEnd_439609 := by
    simpa [prefixWord, tailWord_439609, baseEnd_439609] using wordTrace_append hprefix tailTrace_439609
  have hstable : (prefixWord ++ tailWord_439609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439609).length < 2 ^ (prefixWord ++ tailWord_439609).sum := by decide
  have hdescent : baseEnd_439609 < baseStart_439609 := by decide
  rcases family_descends (prefixWord ++ tailWord_439609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439623 : List Nat := [1, 1, 4, 1, 2, 5, 2, 1, 4]
def baseStart_439623 : Nat := 118140960795 + 439623 * 2 ^ 59
def prefixEnd_439623 : Nat := 4983230072969 + 3 ^ 40 * 439623 * 2
def baseEnd_439623 : Nat := 100327958120728314084763

theorem tailTrace_439623 : CollatzResearch.WordTrace tailWord_439623 prefixEnd_439623 100327958120728314084763 := by
  unfold tailWord_439623
  simp only [CollatzResearch.WordTrace]
  refine ⟨16034368086328427475955523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10689578724218951650637015 16034368086328427475955523)
  ·
    refine ⟨24051552129492641213933285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16034368086328427475955523 24051552129492641213933285)
    ·
      refine ⟨4509666024279870227612491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24051552129492641213933285 4509666024279870227612491)
      ·
        refine ⟨6764499036419805341418737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4509666024279870227612491 6764499036419805341418737)
        ·
          refine ⟨5073374277314854006064053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6764499036419805341418737 5073374277314854006064053)
          ·
            refine ⟨475628838498267563068505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5073374277314854006064053 475628838498267563068505)
            ·
              refine ⟨356721628873700672301379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475628838498267563068505 356721628873700672301379)
              ·
                refine ⟨535082443310551008452069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356721628873700672301379 535082443310551008452069)
                ·
                  refine ⟨100327958120728314084763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 535082443310551008452069 100327958120728314084763)
                  ·
                    rfl

theorem cell21_439623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 4].length) (baseStart_439623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439623 prefixEnd_439623 := by exact prefixLift 439623
  have htrace : WordTrace (prefixWord ++ tailWord_439623) baseStart_439623 baseEnd_439623 := by
    simpa [prefixWord, tailWord_439623, baseEnd_439623] using wordTrace_append hprefix tailTrace_439623
  have hstable : (prefixWord ++ tailWord_439623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439623).length < 2 ^ (prefixWord ++ tailWord_439623).sum := by decide
  have hdescent : baseEnd_439623 < baseStart_439623 := by decide
  rcases family_descends (prefixWord ++ tailWord_439623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439634 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 7]
def baseStart_439634 : Nat := 118140960795 + 439634 * 2 ^ 59
def prefixEnd_439634 : Nat := 4983230072969 + 3 ^ 40 * 439634 * 2
def baseEnd_439634 : Nat := 100330468470594739401407

theorem tailTrace_439634 : CollatzResearch.WordTrace tailWord_439634 prefixEnd_439634 100330468470594739401407 := by
  unfold tailWord_439634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4008692322322144088651489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10689846192859050903070637 4008692322322144088651489)
  ·
    refine ⟨3006519241741608066488617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4008692322322144088651489 3006519241741608066488617)
    ·
      refine ⟨2254889431306206049866463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3006519241741608066488617 2254889431306206049866463)
      ·
        refine ⟨3382334146959309074799695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2254889431306206049866463 3382334146959309074799695)
        ·
          refine ⟨5073501220438963612199543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3382334146959309074799695 5073501220438963612199543)
          ·
            refine ⟨7610251830658445418299315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5073501220438963612199543 7610251830658445418299315)
            ·
              refine ⟨11415377745987668127448973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7610251830658445418299315 11415377745987668127448973)
              ·
                refine ⟨4280766654745375547793365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11415377745987668127448973 4280766654745375547793365)
                ·
                  refine ⟨100330468470594739401407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4280766654745375547793365 100330468470594739401407)
                  ·
                    rfl

theorem cell21_439634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_439634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439634 prefixEnd_439634 := by exact prefixLift 439634
  have htrace : WordTrace (prefixWord ++ tailWord_439634) baseStart_439634 baseEnd_439634 := by
    simpa [prefixWord, tailWord_439634, baseEnd_439634] using wordTrace_append hprefix tailTrace_439634
  have hstable : (prefixWord ++ tailWord_439634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439634).length < 2 ^ (prefixWord ++ tailWord_439634).sum := by decide
  have hdescent : baseEnd_439634 < baseStart_439634 := by decide
  rcases family_descends (prefixWord ++ tailWord_439634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439665 : List Nat := [1, 2, 2, 2, 1, 2, 3, 4, 4]
def baseStart_439665 : Nat := 118140960795 + 439665 * 2 ^ 59
def prefixEnd_439665 : Nat := 4983230072969 + 3 ^ 40 * 439665 * 2
def baseEnd_439665 : Nat := 100337543092945574384677

theorem tailTrace_439665 : CollatzResearch.WordTrace tailWord_439665 prefixEnd_439665 100337543092945574384677 := by
  unfold tailWord_439665
  simp only [CollatzResearch.WordTrace]
  refine ⟨16035899952176268648984449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10690599968117512432656299 16035899952176268648984449)
  ·
    refine ⟨12026924964132201486738337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16035899952176268648984449 12026924964132201486738337)
    ·
      refine ⟨9020193723099151115053753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12026924964132201486738337 9020193723099151115053753)
      ·
        refine ⟨6765145292324363336290315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9020193723099151115053753 6765145292324363336290315)
        ·
          refine ⟨10147717938486545004435473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6765145292324363336290315 10147717938486545004435473)
          ·
            refine ⟨7610788453864908753326605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10147717938486545004435473 7610788453864908753326605)
            ·
              refine ⟨2854045670199340782497477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7610788453864908753326605 2854045670199340782497477)
              ·
                refine ⟨535133563162376396718277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2854045670199340782497477 535133563162376396718277)
                ·
                  refine ⟨100337543092945574384677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 535133563162376396718277 100337543092945574384677)
                  ·
                    rfl

theorem cell21_439665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_439665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439665 prefixEnd_439665 := by exact prefixLift 439665
  have htrace : WordTrace (prefixWord ++ tailWord_439665) baseStart_439665 baseEnd_439665 := by
    simpa [prefixWord, tailWord_439665, baseEnd_439665] using wordTrace_append hprefix tailTrace_439665
  have hstable : (prefixWord ++ tailWord_439665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439665).length < 2 ^ (prefixWord ++ tailWord_439665).sum := by decide
  have hdescent : baseEnd_439665 < baseStart_439665 := by decide
  rcases family_descends (prefixWord ++ tailWord_439665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439789 : List Nat := [1, 5, 1, 3, 2, 1, 2, 6]
def baseStart_439789 : Nat := 118140960795 + 439789 * 2 ^ 59
def prefixEnd_439789 : Nat := 4983230072969 + 3 ^ 40 * 439789 * 2
def baseEnd_439789 : Nat := 33455280527449638105919

theorem tailTrace_439789 : CollatzResearch.WordTrace tailWord_439789 prefixEnd_439789 33455280527449638105919 := by
  unfold tailWord_439789
  simp only [CollatzResearch.WordTrace]
  refine ⟨16040422603727037826498421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10693615069151358550998947 16040422603727037826498421)
  ·
    refine ⟨1503789619099409796234227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16040422603727037826498421 1503789619099409796234227)
    ·
      refine ⟨2255684428649114694351341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1503789619099409796234227 2255684428649114694351341)
      ·
        refine ⟨845881660743418010381753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2255684428649114694351341 845881660743418010381753)
        ·
          refine ⟨634411245557563507786315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 845881660743418010381753 634411245557563507786315)
          ·
            refine ⟨951616868336345261679473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634411245557563507786315 951616868336345261679473)
            ·
              refine ⟨713712651252258946259605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951616868336345261679473 713712651252258946259605)
              ·
                refine ⟨33455280527449638105919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 713712651252258946259605 33455280527449638105919)
                ·
                  rfl

theorem cell21_439789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 6].length) (baseStart_439789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_439789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_439789 prefixEnd_439789 := by exact prefixLift 439789
  have htrace : WordTrace (prefixWord ++ tailWord_439789) baseStart_439789 baseEnd_439789 := by
    simpa [prefixWord, tailWord_439789, baseEnd_439789] using wordTrace_append hprefix tailTrace_439789
  have hstable : (prefixWord ++ tailWord_439789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439789).length < 2 ^ (prefixWord ++ tailWord_439789).sum := by decide
  have hdescent : baseEnd_439789 < baseStart_439789 := by decide
  rcases family_descends (prefixWord ++ tailWord_439789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440006 : List Nat := [6, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_440006 : Nat := 118140960795 + 440006 * 2 ^ 59
def prefixEnd_440006 : Nat := 4983230072969 + 3 ^ 40 * 440006 * 2
def baseEnd_440006 : Nat := 100415363938804759200647

theorem tailTrace_440006 : CollatzResearch.WordTrace tailWord_440006 prefixEnd_440006 100415363938804759200647 := by
  unfold tailWord_440006
  simp only [CollatzResearch.WordTrace]
  refine ⟨501510538873152621473371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10698891495960589258098581 501510538873152621473371)
  ·
    refine ⟨752265808309728932210057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 501510538873152621473371 752265808309728932210057)
    ·
      refine ⟨564199356232296699157543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 752265808309728932210057 564199356232296699157543)
      ·
        refine ⟨846299034348445048736315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564199356232296699157543 846299034348445048736315)
        ·
          refine ⟨1269448551522667573104473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846299034348445048736315 1269448551522667573104473)
          ·
            refine ⟨952086413642000679828355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1269448551522667573104473 952086413642000679828355)
            ·
              refine ⟨1428129620463001019742533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952086413642000679828355 1428129620463001019742533)
              ·
                refine ⟨267774303836812691201725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1428129620463001019742533 267774303836812691201725)
                ·
                  refine ⟨100415363938804759200647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267774303836812691201725 100415363938804759200647)
                  ·
                    rfl

theorem cell21_440006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_440006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_440006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_440006 prefixEnd_440006 := by exact prefixLift 440006
  have htrace : WordTrace (prefixWord ++ tailWord_440006) baseStart_440006 baseEnd_440006 := by
    simpa [prefixWord, tailWord_440006, baseEnd_440006] using wordTrace_append hprefix tailTrace_440006
  have hstable : (prefixWord ++ tailWord_440006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440006).length < 2 ^ (prefixWord ++ tailWord_440006).sum := by decide
  have hdescent : baseEnd_440006 < baseStart_440006 := by decide
  rcases family_descends (prefixWord ++ tailWord_440006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440014 : List Nat := [4, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_440014 : Nat := 118140960795 + 440014 * 2 ^ 59
def prefixEnd_440014 : Nat := 4983230072969 + 3 ^ 40 * 440014 * 2
def baseEnd_440014 : Nat := 100417189647798523067297

theorem tailTrace_440014 : CollatzResearch.WordTrace tailWord_440014 prefixEnd_440014 100417189647798523067297 := by
  unfold tailWord_440014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2006078628488987656679887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10699086018607934168959397 2006078628488987656679887)
  ·
    refine ⟨3009117942733481485019831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2006078628488987656679887 3009117942733481485019831)
    ·
      refine ⟨4513676914100222227529747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3009117942733481485019831 4513676914100222227529747)
      ·
        refine ⟨6770515371150333341294621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4513676914100222227529747 6770515371150333341294621)
        ·
          refine ⟨2538943264181375002985483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6770515371150333341294621 2538943264181375002985483)
          ·
            refine ⟨3808414896272062504478225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2538943264181375002985483 3808414896272062504478225)
            ·
              refine ⟨2856311172204046878358669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3808414896272062504478225 2856311172204046878358669)
              ·
                refine ⟨1071116689576517579384501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2856311172204046878358669 1071116689576517579384501)
                ·
                  refine ⟨100417189647798523067297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1071116689576517579384501 100417189647798523067297)
                  ·
                    rfl

theorem cell21_440014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_440014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_440014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_440014 prefixEnd_440014 := by exact prefixLift 440014
  have htrace : WordTrace (prefixWord ++ tailWord_440014) baseStart_440014 baseEnd_440014 := by
    simpa [prefixWord, tailWord_440014, baseEnd_440014] using wordTrace_append hprefix tailTrace_440014
  have hstable : (prefixWord ++ tailWord_440014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440014).length < 2 ^ (prefixWord ++ tailWord_440014).sum := by decide
  have hdescent : baseEnd_440014 < baseStart_440014 := by decide
  rcases family_descends (prefixWord ++ tailWord_440014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440062 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_440062 : Nat := 118140960795 + 440062 * 2 ^ 59
def prefixEnd_440062 : Nat := 4983230072969 + 3 ^ 40 * 440062 * 2
def baseEnd_440062 : Nat := 100428143901761106267199

theorem tailTrace_440062 : CollatzResearch.WordTrace tailWord_440062 prefixEnd_440062 100428143901761106267199 := by
  unfold tailWord_440062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2006297466467250681398305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10700253154492003634124293 2006297466467250681398305)
  ·
    refine ⟨1504723099850438011048729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2006297466467250681398305 1504723099850438011048729)
    ·
      refine ⟨1128542324887828508286547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1504723099850438011048729 1128542324887828508286547)
      ·
        refine ⟨1692813487331742762429821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1128542324887828508286547 1692813487331742762429821)
        ·
          refine ⟨634805057749403535911183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1692813487331742762429821 634805057749403535911183)
          ·
            refine ⟨952207586624105303866775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634805057749403535911183 952207586624105303866775)
            ·
              refine ⟨1428311379936157955800163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952207586624105303866775 1428311379936157955800163)
              ·
                refine ⟨2142467069904236933700245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428311379936157955800163 2142467069904236933700245)
                ·
                  refine ⟨100428143901761106267199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2142467069904236933700245 100428143901761106267199)
                  ·
                    rfl

theorem cell21_440062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_440062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_440062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_440062 prefixEnd_440062 := by exact prefixLift 440062
  have htrace : WordTrace (prefixWord ++ tailWord_440062) baseStart_440062 baseEnd_440062 := by
    simpa [prefixWord, tailWord_440062, baseEnd_440062] using wordTrace_append hprefix tailTrace_440062
  have hstable : (prefixWord ++ tailWord_440062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440062).length < 2 ^ (prefixWord ++ tailWord_440062).sum := by decide
  have hdescent : baseEnd_440062 < baseStart_440062 := by decide
  rcases family_descends (prefixWord ++ tailWord_440062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440090 : List Nat := [3, 1, 1, 3, 2, 2, 2, 2, 5]
def baseStart_440090 : Nat := 118140960795 + 440090 * 2 ^ 59
def prefixEnd_440090 : Nat := 4983230072969 + 3 ^ 40 * 440090 * 2
def baseEnd_440090 : Nat := 100434533883239279800475

theorem tailTrace_440090 : CollatzResearch.WordTrace tailWord_440090 prefixEnd_440090 100434533883239279800475 := by
  unfold tailWord_440090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4012850243909141558301431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10700933983757710822137149 4012850243909141558301431)
  ·
    refine ⟨6019275365863712337452147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4012850243909141558301431 6019275365863712337452147)
    ·
      refine ⟨9028913048795568506178221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6019275365863712337452147 9028913048795568506178221)
      ·
        refine ⟨3385842393298338189816833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9028913048795568506178221 3385842393298338189816833)
        ·
          refine ⟨2539381794973753642362625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3385842393298338189816833 2539381794973753642362625)
          ·
            refine ⟨1904536346230315231771969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2539381794973753642362625 1904536346230315231771969)
            ·
              refine ⟨1428402259672736423828977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1904536346230315231771969 1428402259672736423828977)
              ·
                refine ⟨1071301694754552317871733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1428402259672736423828977 1071301694754552317871733)
                ·
                  refine ⟨100434533883239279800475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1071301694754552317871733 100434533883239279800475)
                  ·
                    rfl

theorem cell21_440090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_440090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_440090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_440090 prefixEnd_440090 := by exact prefixLift 440090
  have htrace : WordTrace (prefixWord ++ tailWord_440090) baseStart_440090 baseEnd_440090 := by
    simpa [prefixWord, tailWord_440090, baseEnd_440090] using wordTrace_append hprefix tailTrace_440090
  have hstable : (prefixWord ++ tailWord_440090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440090).length < 2 ^ (prefixWord ++ tailWord_440090).sum := by decide
  have hdescent : baseEnd_440090 < baseStart_440090 := by decide
  rcases family_descends (prefixWord ++ tailWord_440090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440287 : List Nat := [1, 1, 2, 3, 4, 3, 7]
def baseStart_440287 : Nat := 118140960795 + 440287 * 2 ^ 59
def prefixEnd_440287 : Nat := 4983230072969 + 3 ^ 40 * 440287 * 2
def baseEnd_440287 : Nat := 11164387996356746112971

theorem tailTrace_440287 : CollatzResearch.WordTrace tailWord_440287 prefixEnd_440287 11164387996356746112971 := by
  unfold tailWord_440287
  simp only [CollatzResearch.WordTrace]
  refine ⟨16058586155922868878127115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10705724103948579252084743 16058586155922868878127115)
  ·
    refine ⟨24087879233884303317190673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16058586155922868878127115 24087879233884303317190673)
    ·
      refine ⟨18065909425413227487893005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24087879233884303317190673 18065909425413227487893005)
      ·
        refine ⟨6774716034529960307959877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18065909425413227487893005 6774716034529960307959877)
        ·
          refine ⟨1270259256474367557742477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6774716034529960307959877 1270259256474367557742477)
          ·
            refine ⟨476347221177887834153429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1270259256474367557742477 476347221177887834153429)
            ·
              refine ⟨11164387996356746112971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 476347221177887834153429 11164387996356746112971)
              ·
                rfl

theorem cell21_440287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 7].length) (baseStart_440287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_440287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_440287 prefixEnd_440287 := by exact prefixLift 440287
  have htrace : WordTrace (prefixWord ++ tailWord_440287) baseStart_440287 baseEnd_440287 := by
    simpa [prefixWord, tailWord_440287, baseEnd_440287] using wordTrace_append hprefix tailTrace_440287
  have hstable : (prefixWord ++ tailWord_440287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440287).length < 2 ^ (prefixWord ++ tailWord_440287).sum := by decide
  have hdescent : baseEnd_440287 < baseStart_440287 := by decide
  rcases family_descends (prefixWord ++ tailWord_440287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440346 : List Nat := [3, 1, 1, 3, 1, 12]
def baseStart_440346 : Nat := 118140960795 + 440346 * 2 ^ 59
def prefixEnd_440346 : Nat := 4983230072969 + 3 ^ 40 * 440346 * 2
def baseEnd_440346 : Nat := 3721961354482952723455

theorem tailTrace_440346 : CollatzResearch.WordTrace tailWord_440346 prefixEnd_440346 3721961354482952723455 := by
  unfold tailWord_440346
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015184515677280488631223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10707158708472747969683261 4015184515677280488631223)
  ·
    refine ⟨6022776773515920732946835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4015184515677280488631223 6022776773515920732946835)
    ·
      refine ⟨9034165160273881099420253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6022776773515920732946835 9034165160273881099420253)
      ·
        refine ⟨3387811935102705412282595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9034165160273881099420253 3387811935102705412282595)
        ·
          refine ⟨5081717902654058118423893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3387811935102705412282595 5081717902654058118423893)
          ·
            refine ⟨3721961354482952723455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5081717902654058118423893 3721961354482952723455)
            ·
              rfl

theorem cell21_440346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 12].length) (baseStart_440346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_440346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_440346 prefixEnd_440346 := by exact prefixLift 440346
  have htrace : WordTrace (prefixWord ++ tailWord_440346) baseStart_440346 baseEnd_440346 := by
    simpa [prefixWord, tailWord_440346, baseEnd_440346] using wordTrace_append hprefix tailTrace_440346
  have hstable : (prefixWord ++ tailWord_440346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440346).length < 2 ^ (prefixWord ++ tailWord_440346).sum := by decide
  have hdescent : baseEnd_440346 < baseStart_440346 := by decide
  rcases family_descends (prefixWord ++ tailWord_440346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440349 : List Nat := [1, 4, 2, 2, 2, 1, 1, 4, 4]
def baseStart_440349 : Nat := 118140960795 + 440349 * 2 ^ 59
def prefixEnd_440349 : Nat := 4983230072969 + 3 ^ 40 * 440349 * 2
def baseEnd_440349 : Nat := 100493641211912384983279

theorem tailTrace_440349 : CollatzResearch.WordTrace tailWord_440349 prefixEnd_440349 100493641211912384983279 := by
  unfold tailWord_440349
  simp only [CollatzResearch.WordTrace]
  refine ⟨16060847481698253466884101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10707231654465502311256067 16060847481698253466884101)
  ·
    refine ⟨3011408902818422525040769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16060847481698253466884101 3011408902818422525040769)
    ·
      refine ⟨2258556677113816893780577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3011408902818422525040769 2258556677113816893780577)
      ·
        refine ⟨1693917507835362670335433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2258556677113816893780577 1693917507835362670335433)
        ·
          refine ⟨1270438130876522002751575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1693917507835362670335433 1270438130876522002751575)
          ·
            refine ⟨1905657196314783004127363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270438130876522002751575 1905657196314783004127363)
            ·
              refine ⟨2858485794472174506191045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905657196314783004127363 2858485794472174506191045)
              ·
                refine ⟨535966086463532719910821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2858485794472174506191045 535966086463532719910821)
                ·
                  refine ⟨100493641211912384983279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 535966086463532719910821 100493641211912384983279)
                  ·
                    rfl

theorem cell21_440349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_440349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_440349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_440349 prefixEnd_440349 := by exact prefixLift 440349
  have htrace : WordTrace (prefixWord ++ tailWord_440349) baseStart_440349 baseEnd_440349 := by
    simpa [prefixWord, tailWord_440349, baseEnd_440349] using wordTrace_append hprefix tailTrace_440349
  have hstable : (prefixWord ++ tailWord_440349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440349).length < 2 ^ (prefixWord ++ tailWord_440349).sum := by decide
  have hdescent : baseEnd_440349 < baseStart_440349 := by decide
  rcases family_descends (prefixWord ++ tailWord_440349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440408 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 6]
def baseStart_440408 : Nat := 118140960795 + 440408 * 2 ^ 59
def prefixEnd_440408 : Nat := 4983230072969 + 3 ^ 40 * 440408 * 2
def baseEnd_440408 : Nat := 100507105815741393499825

theorem tailTrace_440408 : CollatzResearch.WordTrace tailWord_440408 prefixEnd_440408 100507105815741393499825 := by
  unfold tailWord_440408
  simp only [CollatzResearch.WordTrace]
  refine ⟨8031499694242253271640939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10708666258989671028854585 8031499694242253271640939)
  ·
    refine ⟨12047249541363379907461409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8031499694242253271640939 12047249541363379907461409)
    ·
      refine ⟨9035437156022534930596057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12047249541363379907461409 9035437156022534930596057)
      ·
        refine ⟨6776577867016901197947043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9035437156022534930596057 6776577867016901197947043)
        ·
          refine ⟨10164866800525351796920565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6776577867016901197947043 10164866800525351796920565)
          ·
            refine ⟨952956262549251730961303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10164866800525351796920565 952956262549251730961303)
            ·
              refine ⟨1429434393823877596441955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952956262549251730961303 1429434393823877596441955)
              ·
                refine ⟨2144151590735816394662933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1429434393823877596441955 2144151590735816394662933)
                ·
                  refine ⟨100507105815741393499825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2144151590735816394662933 100507105815741393499825)
                  ·
                    rfl

theorem cell21_440408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_440408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_440408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_440408 prefixEnd_440408 := by exact prefixLift 440408
  have htrace : WordTrace (prefixWord ++ tailWord_440408) baseStart_440408 baseEnd_440408 := by
    simpa [prefixWord, tailWord_440408, baseEnd_440408] using wordTrace_append hprefix tailTrace_440408
  have hstable : (prefixWord ++ tailWord_440408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440408).length < 2 ^ (prefixWord ++ tailWord_440408).sum := by decide
  have hdescent : baseEnd_440408 < baseStart_440408 := by decide
  rcases family_descends (prefixWord ++ tailWord_440408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440425 : List Nat := [1, 2, 1, 1, 1, 5, 5, 1, 4]
def baseStart_440425 : Nat := 118140960795 + 440425 * 2 ^ 59
def prefixEnd_440425 : Nat := 4983230072969 + 3 ^ 40 * 440425 * 2
def baseEnd_440425 : Nat := 100510985447353141716457

theorem tailTrace_440425 : CollatzResearch.WordTrace tailWord_440425 prefixEnd_440425 100510985447353141716457 := by
  unfold tailWord_440425
  simp only [CollatzResearch.WordTrace]
  refine ⟨16063619429422918446650729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10709079619615278964433819 16063619429422918446650729)
  ·
    refine ⟨12047714572067188834988047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16063619429422918446650729 12047714572067188834988047)
    ·
      refine ⟨18071571858100783252482071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12047714572067188834988047 18071571858100783252482071)
      ·
        refine ⟨27107357787151174878723107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18071571858100783252482071 27107357787151174878723107)
        ·
          refine ⟨40661036680726762318084661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27107357787151174878723107 40661036680726762318084661)
          ·
            refine ⟨3811972188818133967320437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40661036680726762318084661 3811972188818133967320437)
            ·
              refine ⟨357372392701700059436291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3811972188818133967320437 357372392701700059436291)
              ·
                refine ⟨536058589052550089154437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357372392701700059436291 536058589052550089154437)
                ·
                  refine ⟨100510985447353141716457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 536058589052550089154437 100510985447353141716457)
                  ·
                    rfl

theorem cell21_440425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 4].length) (baseStart_440425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_440425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_440425 prefixEnd_440425 := by exact prefixLift 440425
  have htrace : WordTrace (prefixWord ++ tailWord_440425) baseStart_440425 baseEnd_440425 := by
    simpa [prefixWord, tailWord_440425, baseEnd_440425] using wordTrace_append hprefix tailTrace_440425
  have hstable : (prefixWord ++ tailWord_440425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440425).length < 2 ^ (prefixWord ++ tailWord_440425).sum := by decide
  have hdescent : baseEnd_440425 < baseStart_440425 := by decide
  rcases family_descends (prefixWord ++ tailWord_440425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440439 : List Nat := [1, 1, 3, 1, 1, 5, 4, 5]
def baseStart_440439 : Nat := 118140960795 + 440439 * 2 ^ 59
def prefixEnd_440439 : Nat := 4983230072969 + 3 ^ 40 * 440439 * 2
def baseEnd_440439 : Nat := 33504726812697409494365

theorem tailTrace_440439 : CollatzResearch.WordTrace tailWord_440439 prefixEnd_440439 33504726812697409494365 := by
  unfold tailWord_440439
  simp only [CollatzResearch.WordTrace]
  refine ⟨16064130051372198837660371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10709420034248132558440247 16064130051372198837660371)
  ·
    refine ⟨24096195077058298256490557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16064130051372198837660371 24096195077058298256490557)
    ·
      refine ⟨9036073153896861846183959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24096195077058298256490557 9036073153896861846183959)
      ·
        refine ⟨13554109730845292769275939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9036073153896861846183959 13554109730845292769275939)
        ·
          refine ⟨20331164596267939153913909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13554109730845292769275939 20331164596267939153913909)
          ·
            refine ⟨1906046680900119295679429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20331164596267939153913909 1906046680900119295679429)
            ·
              refine ⟨357383752668772367939893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1906046680900119295679429 357383752668772367939893)
              ·
                refine ⟨33504726812697409494365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 357383752668772367939893 33504726812697409494365)
                ·
                  rfl

theorem cell21_440439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 5].length) (baseStart_440439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_440439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_440439 prefixEnd_440439 := by exact prefixLift 440439
  have htrace : WordTrace (prefixWord ++ tailWord_440439) baseStart_440439 baseEnd_440439 := by
    simpa [prefixWord, tailWord_440439, baseEnd_440439] using wordTrace_append hprefix tailTrace_440439
  have hstable : (prefixWord ++ tailWord_440439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440439).length < 2 ^ (prefixWord ++ tailWord_440439).sum := by decide
  have hdescent : baseEnd_440439 < baseStart_440439 := by decide
  rcases family_descends (prefixWord ++ tailWord_440439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440498 : List Nat := [3, 2, 1, 1, 1, 3, 1, 9]
def baseStart_440498 : Nat := 118140960795 + 440498 * 2 ^ 59
def prefixEnd_440498 : Nat := 4983230072969 + 3 ^ 40 * 440498 * 2
def baseEnd_440498 : Nat := 33509215013973745666547

theorem tailTrace_440498 : CollatzResearch.WordTrace tailWord_440498 prefixEnd_440498 33509215013973745666547 := by
  unfold tailWord_440498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4016570489539612978514537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10710854638772301276038765 4016570489539612978514537)
  ·
    refine ⟨3012427867154709733885903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4016570489539612978514537 3012427867154709733885903)
    ·
      refine ⟨4518641800732064600828855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3012427867154709733885903 4518641800732064600828855)
      ·
        refine ⟨6777962701098096901243283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4518641800732064600828855 6777962701098096901243283)
        ·
          refine ⟨10166944051647145351864925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6777962701098096901243283 10166944051647145351864925)
          ·
            refine ⟨3812604019367679506949347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10166944051647145351864925 3812604019367679506949347)
            ·
              refine ⟨5718906029051519260424021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3812604019367679506949347 5718906029051519260424021)
              ·
                refine ⟨33509215013973745666547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5718906029051519260424021 33509215013973745666547)
                ·
                  rfl

theorem cell21_440498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_440498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_440498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_440498 prefixEnd_440498 := by exact prefixLift 440498
  have htrace : WordTrace (prefixWord ++ tailWord_440498) baseStart_440498 baseEnd_440498 := by
    simpa [prefixWord, tailWord_440498, baseEnd_440498] using wordTrace_append hprefix tailTrace_440498
  have hstable : (prefixWord ++ tailWord_440498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440498).length < 2 ^ (prefixWord ++ tailWord_440498).sum := by decide
  have hdescent : baseEnd_440498 < baseStart_440498 := by decide
  rcases family_descends (prefixWord ++ tailWord_440498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440543 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 8]
def baseStart_440543 : Nat := 118140960795 + 440543 * 2 ^ 59
def prefixEnd_440543 : Nat := 4983230072969 + 3 ^ 40 * 440543 * 2
def baseEnd_440543 : Nat := 100537914655011158749549

theorem tailTrace_440543 : CollatzResearch.WordTrace tailWord_440543 prefixEnd_440543 100537914655011158749549 := by
  unfold tailWord_440543
  simp only [CollatzResearch.WordTrace]
  refine ⟨16067923242995424599446283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10711948828663616399630855 16067923242995424599446283)
  ·
    refine ⟨24101884864493136899169425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16067923242995424599446283 24101884864493136899169425)
    ·
      refine ⟨18076413648369852674377069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24101884864493136899169425 18076413648369852674377069)
      ·
        refine ⟨6778655118138694752891401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18076413648369852674377069 6778655118138694752891401)
        ·
          refine ⟨5083991338604021064668551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6778655118138694752891401 5083991338604021064668551)
          ·
            refine ⟨7625987007906031597002827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5083991338604021064668551 7625987007906031597002827)
            ·
              refine ⟨11438980511859047395504241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7625987007906031597002827 11438980511859047395504241)
              ·
                refine ⟨8579235383894285546628181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11438980511859047395504241 8579235383894285546628181)
                ·
                  refine ⟨100537914655011158749549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8579235383894285546628181 100537914655011158749549)
                  ·
                    rfl

theorem cell21_440543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 8].length) (baseStart_440543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_440543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_440543 prefixEnd_440543 := by exact prefixLift 440543
  have htrace : WordTrace (prefixWord ++ tailWord_440543) baseStart_440543 baseEnd_440543 := by
    simpa [prefixWord, tailWord_440543, baseEnd_440543] using wordTrace_append hprefix tailTrace_440543
  have hstable : (prefixWord ++ tailWord_440543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440543).length < 2 ^ (prefixWord ++ tailWord_440543).sum := by decide
  have hdescent : baseEnd_440543 < baseStart_440543 := by decide
  rcases family_descends (prefixWord ++ tailWord_440543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440608 : List Nat := [2, 1, 1, 5, 2, 3, 2, 5]
def baseStart_440608 : Nat := 118140960795 + 440608 * 2 ^ 59
def prefixEnd_440608 : Nat := 4983230072969 + 3 ^ 40 * 440608 * 2
def baseEnd_440608 : Nat := 33517582846861830055361

theorem tailTrace_440608 : CollatzResearch.WordTrace tailWord_440608 prefixEnd_440608 33517582846861830055361 := by
  unfold tailWord_440608
  simp only [CollatzResearch.WordTrace]
  refine ⟨8035146993879970350281239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10713529325173293800374985 8035146993879970350281239)
  ·
    refine ⟨12052720490819955525421859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8035146993879970350281239 12052720490819955525421859)
    ·
      refine ⟨18079080736229933288132789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12052720490819955525421859 18079080736229933288132789)
      ·
        refine ⟨1694913819021556245762449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18079080736229933288132789 1694913819021556245762449)
        ·
          refine ⟨1271185364266167184321837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1694913819021556245762449 1271185364266167184321837)
          ·
            refine ⟨476694511599812694120689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1271185364266167184321837 476694511599812694120689)
            ·
              refine ⟨357520883699859520590517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476694511599812694120689 357520883699859520590517)
              ·
                refine ⟨33517582846861830055361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 357520883699859520590517 33517582846861830055361)
                ·
                  rfl

theorem cell21_440608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 5].length) (baseStart_440608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_440608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_440608 prefixEnd_440608 := by exact prefixLift 440608
  have htrace : WordTrace (prefixWord ++ tailWord_440608) baseStart_440608 baseEnd_440608 := by
    simpa [prefixWord, tailWord_440608, baseEnd_440608] using wordTrace_append hprefix tailTrace_440608
  have hstable : (prefixWord ++ tailWord_440608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440608).length < 2 ^ (prefixWord ++ tailWord_440608).sum := by decide
  have hdescent : baseEnd_440608 < baseStart_440608 := by decide
  rcases family_descends (prefixWord ++ tailWord_440608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440636 : List Nat := [2, 2, 2, 2, 1, 2, 2, 4, 4]
def baseStart_440636 : Nat := 118140960795 + 440636 * 2 ^ 59
def prefixEnd_440636 : Nat := 4983230072969 + 3 ^ 40 * 440636 * 2
def baseEnd_440636 : Nat := 100559138522063663699359

theorem tailTrace_440636 : CollatzResearch.WordTrace tailWord_440636 prefixEnd_440636 100559138522063663699359 := by
  unfold tailWord_440636
  simp only [CollatzResearch.WordTrace]
  refine ⟨8035657615829250741290881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10714210154439000988387841 8035657615829250741290881)
  ·
    refine ⟨6026743211871938055968161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8035657615829250741290881 6026743211871938055968161)
    ·
      refine ⟨4520057408903953541976121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6026743211871938055968161 4520057408903953541976121)
      ·
        refine ⟨3390043056677965156482091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4520057408903953541976121 3390043056677965156482091)
        ·
          refine ⟨5085064585016947734723137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3390043056677965156482091 5085064585016947734723137)
          ·
            refine ⟨3813798438762710801042353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5085064585016947734723137 3813798438762710801042353)
            ·
              refine ⟨2860348829072033100781765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3813798438762710801042353 2860348829072033100781765)
              ·
                refine ⟨536315405451006206396581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2860348829072033100781765 536315405451006206396581)
                ·
                  refine ⟨100559138522063663699359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 536315405451006206396581 100559138522063663699359)
                  ·
                    rfl

theorem cell21_440636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_440636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_440636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_440636 prefixEnd_440636 := by exact prefixLift 440636
  have htrace : WordTrace (prefixWord ++ tailWord_440636) baseStart_440636 baseEnd_440636 := by
    simpa [prefixWord, tailWord_440636, baseEnd_440636] using wordTrace_append hprefix tailTrace_440636
  have hstable : (prefixWord ++ tailWord_440636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440636).length < 2 ^ (prefixWord ++ tailWord_440636).sum := by decide
  have hdescent : baseEnd_440636 < baseStart_440636 := by decide
  rcases family_descends (prefixWord ++ tailWord_440636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440639 : List Nat := [1, 1, 2, 2, 4, 1, 5, 2, 3]
def baseStart_440639 : Nat := 118140960795 + 440639 * 2 ^ 59
def prefixEnd_440639 : Nat := 4983230072969 + 3 ^ 40 * 440639 * 2
def baseEnd_440639 : Nat := 100559823162936325149353

theorem tailTrace_440639 : CollatzResearch.WordTrace tailWord_440639 prefixEnd_440639 100559823162936325149353 := by
  unfold tailWord_440639
  simp only [CollatzResearch.WordTrace]
  refine ⟨16071424650647632994940971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10714283100431755329960647 16071424650647632994940971)
  ·
    refine ⟨24107136975971449492411457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16071424650647632994940971 24107136975971449492411457)
    ·
      refine ⟨18080352731978587119308593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24107136975971449492411457 18080352731978587119308593)
      ·
        refine ⟨13560264548983940339481445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18080352731978587119308593 13560264548983940339481445)
        ·
          refine ⟨2542549602934488813652771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13560264548983940339481445 2542549602934488813652771)
          ·
            refine ⟨3813824404401733220479157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2542549602934488813652771 3813824404401733220479157)
            ·
              refine ⟨357546037912662489419921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3813824404401733220479157 357546037912662489419921)
              ·
                refine ⟨268159528434496867064941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357546037912662489419921 268159528434496867064941)
                ·
                  refine ⟨100559823162936325149353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 268159528434496867064941 100559823162936325149353)
                  ·
                    rfl

theorem cell21_440639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 3].length) (baseStart_440639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_440639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_440639 prefixEnd_440639 := by exact prefixLift 440639
  have htrace : WordTrace (prefixWord ++ tailWord_440639) baseStart_440639 baseEnd_440639 := by
    simpa [prefixWord, tailWord_440639, baseEnd_440639] using wordTrace_append hprefix tailTrace_440639
  have hstable : (prefixWord ++ tailWord_440639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440639).length < 2 ^ (prefixWord ++ tailWord_440639).sum := by decide
  have hdescent : baseEnd_440639 < baseStart_440639 := by decide
  rcases family_descends (prefixWord ++ tailWord_440639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440712 : List Nat := [2, 1, 3, 3, 1, 1, 1, 5, 4]
def baseStart_440712 : Nat := 118140960795 + 440712 * 2 ^ 59
def prefixEnd_440712 : Nat := 4983230072969 + 3 ^ 40 * 440712 * 2
def baseEnd_440712 : Nat := 100576482757504420432537

theorem tailTrace_440712 : CollatzResearch.WordTrace tailWord_440712 prefixEnd_440712 100576482757504420432537 := by
  unfold tailWord_440712
  simp only [CollatzResearch.WordTrace]
  refine ⟨8037043589691583231174195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10716058119588777641565593 8037043589691583231174195)
  ·
    refine ⟨12055565384537374846761293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8037043589691583231174195 12055565384537374846761293)
    ·
      refine ⟨4520837019201515567535485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12055565384537374846761293 4520837019201515567535485)
      ·
        refine ⟨1695313882200568337825807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4520837019201515567535485 1695313882200568337825807)
        ·
          refine ⟨2542970823300852506738711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1695313882200568337825807 2542970823300852506738711)
          ·
            refine ⟨3814456234951278760108067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2542970823300852506738711 3814456234951278760108067)
            ·
              refine ⟨5721684352426918140162101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814456234951278760108067 5721684352426918140162101)
              ·
                refine ⟨536407908040023575640197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5721684352426918140162101 536407908040023575640197)
                ·
                  refine ⟨100576482757504420432537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 536407908040023575640197 100576482757504420432537)
                  ·
                    rfl

theorem cell21_440712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_440712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_440712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_440712 prefixEnd_440712 := by exact prefixLift 440712
  have htrace : WordTrace (prefixWord ++ tailWord_440712) baseStart_440712 baseEnd_440712 := by
    simpa [prefixWord, tailWord_440712, baseEnd_440712] using wordTrace_append hprefix tailTrace_440712
  have hstable : (prefixWord ++ tailWord_440712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440712).length < 2 ^ (prefixWord ++ tailWord_440712).sum := by decide
  have hdescent : baseEnd_440712 < baseStart_440712 := by decide
  rcases family_descends (prefixWord ++ tailWord_440712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440788 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 6]
def baseStart_440788 : Nat := 118140960795 + 440788 * 2 ^ 59
def prefixEnd_440788 : Nat := 4983230072969 + 3 ^ 40 * 440788 * 2
def baseEnd_440788 : Nat := 100593826992945177165715

theorem tailTrace_440788 : CollatzResearch.WordTrace tailWord_440788 prefixEnd_440788 100593826992945177165715 := by
  unfold tailWord_440788
  simp only [CollatzResearch.WordTrace]
  refine ⟨8038429563553915721057509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10717906084738554294743345 8038429563553915721057509)
  ·
    refine ⟨1507205543166359197698283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8038429563553915721057509 1507205543166359197698283)
    ·
      refine ⟨2260808314749538796547425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1507205543166359197698283 2260808314749538796547425)
      ·
        refine ⟨1695606236062154097410569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2260808314749538796547425 1695606236062154097410569)
        ·
          refine ⟨1271704677046615573057927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1695606236062154097410569 1271704677046615573057927)
          ·
            refine ⟨1907557015569923359586891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271704677046615573057927 1907557015569923359586891)
            ·
              refine ⟨2861335523354885039380337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1907557015569923359586891 2861335523354885039380337)
              ·
                refine ⟨2146001642516163779535253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2861335523354885039380337 2146001642516163779535253)
                ·
                  refine ⟨100593826992945177165715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2146001642516163779535253 100593826992945177165715)
                  ·
                    rfl

theorem cell21_440788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_440788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_440788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_440788 prefixEnd_440788 := by exact prefixLift 440788
  have htrace : WordTrace (prefixWord ++ tailWord_440788) baseStart_440788 baseEnd_440788 := by
    simpa [prefixWord, tailWord_440788, baseEnd_440788] using wordTrace_append hprefix tailTrace_440788
  have hstable : (prefixWord ++ tailWord_440788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440788).length < 2 ^ (prefixWord ++ tailWord_440788).sum := by decide
  have hdescent : baseEnd_440788 < baseStart_440788 := by decide
  rcases family_descends (prefixWord ++ tailWord_440788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440867 : List Nat := [1, 1, 1, 4, 4, 1, 4, 2, 3]
def baseStart_440867 : Nat := 118140960795 + 440867 * 2 ^ 59
def prefixEnd_440867 : Nat := 4983230072969 + 3 ^ 40 * 440867 * 2
def baseEnd_440867 : Nat := 100611855869258595348887

theorem tailTrace_440867 : CollatzResearch.WordTrace tailWord_440867 prefixEnd_440867 100611855869258595348887 := by
  unfold tailWord_440867
  simp only [CollatzResearch.WordTrace]
  refine ⟨16079740493821627934240855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10719826995881085289493903 16079740493821627934240855)
  ·
    refine ⟨24119610740732441901361283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16079740493821627934240855 24119610740732441901361283)
    ·
      refine ⟨36179416111098662852041925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24119610740732441901361283 36179416111098662852041925)
      ·
        refine ⟨6783640520830999284757861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36179416111098662852041925 6783640520830999284757861)
        ·
          refine ⟨1271932597655812365892099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6783640520830999284757861 1271932597655812365892099)
          ·
            refine ⟨1907898896483718548838149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271932597655812365892099 1907898896483718548838149)
            ·
              refine ⟨357731043090697227907153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1907898896483718548838149 357731043090697227907153)
              ·
                refine ⟨268298282318022920930365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357731043090697227907153 268298282318022920930365)
                ·
                  refine ⟨100611855869258595348887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 268298282318022920930365 100611855869258595348887)
                  ·
                    rfl

theorem cell21_440867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 3].length) (baseStart_440867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_440867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_440867 prefixEnd_440867 := by exact prefixLift 440867
  have htrace : WordTrace (prefixWord ++ tailWord_440867) baseStart_440867 baseEnd_440867 := by
    simpa [prefixWord, tailWord_440867, baseEnd_440867] using wordTrace_append hprefix tailTrace_440867
  have hstable : (prefixWord ++ tailWord_440867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440867).length < 2 ^ (prefixWord ++ tailWord_440867).sum := by decide
  have hdescent : baseEnd_440867 < baseStart_440867 := by decide
  rcases family_descends (prefixWord ++ tailWord_440867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440937 : List Nat := [1, 2, 1, 1, 1, 4, 1, 10]
def baseStart_440937 : Nat := 118140960795 + 440937 * 2 ^ 59
def prefixEnd_440937 : Nat := 4983230072969 + 3 ^ 40 * 440937 * 2
def baseEnd_440937 : Nat := 33542610274318009727359

theorem tailTrace_440937 : CollatzResearch.WordTrace tailWord_440937 prefixEnd_440937 33542610274318009727359 := by
  unfold tailWord_440937
  simp only [CollatzResearch.WordTrace]
  refine ⟨16082293603568029889289065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10721529069045353259526043 16082293603568029889289065)
  ·
    refine ⟨12061720202676022416966799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16082293603568029889289065 12061720202676022416966799)
    ·
      refine ⟨18092580304014033625450199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12061720202676022416966799 18092580304014033625450199)
      ·
        refine ⟨27138870456021050438175299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18092580304014033625450199 27138870456021050438175299)
        ·
          refine ⟨40708305684031575657262949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27138870456021050438175299 40708305684031575657262949)
          ·
            refine ⟨7632807315755920435736803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40708305684031575657262949 7632807315755920435736803)
            ·
              refine ⟨11449210973633880653605205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7632807315755920435736803 11449210973633880653605205)
              ·
                refine ⟨33542610274318009727359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11449210973633880653605205 33542610274318009727359)
                ·
                  rfl

theorem cell21_440937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 10].length) (baseStart_440937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_440937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_440937 prefixEnd_440937 := by exact prefixLift 440937
  have htrace : WordTrace (prefixWord ++ tailWord_440937) baseStart_440937 baseEnd_440937 := by
    simpa [prefixWord, tailWord_440937, baseEnd_440937] using wordTrace_append hprefix tailTrace_440937
  have hstable : (prefixWord ++ tailWord_440937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440937).length < 2 ^ (prefixWord ++ tailWord_440937).sum := by decide
  have hdescent : baseEnd_440937 < baseStart_440937 := by decide
  rcases family_descends (prefixWord ++ tailWord_440937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441036 : List Nat := [2, 2, 1, 5, 1, 3, 2, 2, 3]
def baseStart_441036 : Nat := 118140960795 + 441036 * 2 ^ 59
def prefixEnd_441036 : Nat := 4983230072969 + 3 ^ 40 * 441036 * 2
def baseEnd_441036 : Nat := 100650423971751857031875

theorem tailTrace_441036 : CollatzResearch.WordTrace tailWord_441036 prefixEnd_441036 100650423971751857031875 := by
  unfold tailWord_441036
  simp only [CollatzResearch.WordTrace]
  refine ⟨8042952215104684898571481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10723936286806246531428641 8042952215104684898571481)
  ·
    refine ⟨6032214161328513673928611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8042952215104684898571481 6032214161328513673928611)
    ·
      refine ⟨9048321241992770510892917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6032214161328513673928611 9048321241992770510892917)
      ·
        refine ⟨848280116436822235396211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9048321241992770510892917 848280116436822235396211)
        ·
          refine ⟨1272420174655233353094317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848280116436822235396211 1272420174655233353094317)
          ·
            refine ⟨477157565495712507410369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1272420174655233353094317 477157565495712507410369)
            ·
              refine ⟨357868174121784380557777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477157565495712507410369 357868174121784380557777)
              ·
                refine ⟨268401130591338285418333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357868174121784380557777 268401130591338285418333)
                ·
                  refine ⟨100650423971751857031875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 268401130591338285418333 100650423971751857031875)
                  ·
                    rfl

theorem cell21_441036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_441036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441036 prefixEnd_441036 := by exact prefixLift 441036
  have htrace : WordTrace (prefixWord ++ tailWord_441036) baseStart_441036 baseEnd_441036 := by
    simpa [prefixWord, tailWord_441036, baseEnd_441036] using wordTrace_append hprefix tailTrace_441036
  have hstable : (prefixWord ++ tailWord_441036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441036).length < 2 ^ (prefixWord ++ tailWord_441036).sum := by decide
  have hdescent : baseEnd_441036 < baseStart_441036 := by decide
  rcases family_descends (prefixWord ++ tailWord_441036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441061 : List Nat := [1, 3, 1, 4, 1, 3, 1, 2, 5]
def baseStart_441061 : Nat := 118140960795 + 441061 * 2 ^ 59
def prefixEnd_441061 : Nat := 4983230072969 + 3 ^ 40 * 441061 * 2
def baseEnd_441061 : Nat := 100656129312357369115157

theorem tailTrace_441061 : CollatzResearch.WordTrace tailWord_441061 prefixEnd_441061 100656129312357369115157 := by
  unfold tailWord_441061
  simp only [CollatzResearch.WordTrace]
  refine ⟨16086816255118799066803037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10724544170079199377868691 16086816255118799066803037)
  ·
    refine ⟨6032556095669549650051139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16086816255118799066803037 6032556095669549650051139)
    ·
      refine ⟨9048834143504324475076709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6032556095669549650051139 9048834143504324475076709)
      ·
        refine ⟨1696656401907060839076883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9048834143504324475076709 1696656401907060839076883)
        ·
          refine ⟨2544984602860591258615325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1696656401907060839076883 2544984602860591258615325)
          ·
            refine ⟨954369226072721721980747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2544984602860591258615325 954369226072721721980747)
            ·
              refine ⟨1431553839109082582971121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954369226072721721980747 1431553839109082582971121)
              ·
                refine ⟨1073665379331811937228341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1431553839109082582971121 1073665379331811937228341)
                ·
                  refine ⟨100656129312357369115157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1073665379331811937228341 100656129312357369115157)
                  ·
                    rfl

theorem cell21_441061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_441061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441061 prefixEnd_441061 := by exact prefixLift 441061
  have htrace : WordTrace (prefixWord ++ tailWord_441061) baseStart_441061 baseEnd_441061 := by
    simpa [prefixWord, tailWord_441061, baseEnd_441061] using wordTrace_append hprefix tailTrace_441061
  have hstable : (prefixWord ++ tailWord_441061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441061).length < 2 ^ (prefixWord ++ tailWord_441061).sum := by decide
  have hdescent : baseEnd_441061 < baseStart_441061 := by decide
  rcases family_descends (prefixWord ++ tailWord_441061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441140 : List Nat := [2, 5, 1, 1, 4, 1, 7]
def baseStart_441140 : Nat := 118140960795 + 441140 * 2 ^ 59
def prefixEnd_441140 : Nat := 4983230072969 + 3 ^ 40 * 441140 * 2
def baseEnd_441140 : Nat := 11186017576518976366481

theorem tailTrace_441140 : CollatzResearch.WordTrace tailWord_441140 prefixEnd_441140 11186017576518976366481 := by
  unfold tailWord_441140
  simp only [CollatzResearch.WordTrace]
  refine ⟨8044848810916297779464437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10726465081221730372619249 8044848810916297779464437)
  ·
    refine ⟨754204576023402916824791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8044848810916297779464437 754204576023402916824791)
    ·
      refine ⟨1131306864035104375237187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 754204576023402916824791 1131306864035104375237187)
      ·
        refine ⟨1696960296052656562855781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1131306864035104375237187 1696960296052656562855781)
        ·
          refine ⟨318180055509873105535459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1696960296052656562855781 318180055509873105535459)
          ·
            refine ⟨477270083264809658303189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318180055509873105535459 477270083264809658303189)
            ·
              refine ⟨11186017576518976366481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 477270083264809658303189 11186017576518976366481)
              ·
                rfl

theorem cell21_441140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 7].length) (baseStart_441140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441140 prefixEnd_441140 := by exact prefixLift 441140
  have htrace : WordTrace (prefixWord ++ tailWord_441140) baseStart_441140 baseEnd_441140 := by
    simpa [prefixWord, tailWord_441140, baseEnd_441140] using wordTrace_append hprefix tailTrace_441140
  have hstable : (prefixWord ++ tailWord_441140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441140).length < 2 ^ (prefixWord ++ tailWord_441140).sum := by decide
  have hdescent : baseEnd_441140 < baseStart_441140 := by decide
  rcases family_descends (prefixWord ++ tailWord_441140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441151 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 6]
def baseStart_441151 : Nat := 118140960795 + 441151 * 2 ^ 59
def prefixEnd_441151 : Nat := 4983230072969 + 3 ^ 40 * 441151 * 2
def baseEnd_441151 : Nat := 100676668538537212614973

theorem tailTrace_441151 : CollatzResearch.WordTrace tailWord_441151 prefixEnd_441151 100676668538537212614973 := by
  unfold tailWord_441151
  simp only [CollatzResearch.WordTrace]
  refine ⟨16090098824792744437579307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10726732549861829625052871 16090098824792744437579307)
  ·
    refine ⟨24135148237189116656368961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16090098824792744437579307 24135148237189116656368961)
    ·
      refine ⟨18101361177891837492276721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24135148237189116656368961 18101361177891837492276721)
      ·
        refine ⟨13576020883418878119207541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18101361177891837492276721 13576020883418878119207541)
        ·
          refine ⟨1272751957820519823675707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13576020883418878119207541 1272751957820519823675707)
          ·
            refine ⟨1909127936730779735513561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1272751957820519823675707 1909127936730779735513561)
            ·
              refine ⟨1431845952548084801635171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1909127936730779735513561 1431845952548084801635171)
              ·
                refine ⟨2147768928822127202452757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1431845952548084801635171 2147768928822127202452757)
                ·
                  refine ⟨100676668538537212614973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2147768928822127202452757 100676668538537212614973)
                  ·
                    rfl

theorem cell21_441151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 6].length) (baseStart_441151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441151 prefixEnd_441151 := by exact prefixLift 441151
  have htrace : WordTrace (prefixWord ++ tailWord_441151) baseStart_441151 baseEnd_441151 := by
    simpa [prefixWord, tailWord_441151, baseEnd_441151] using wordTrace_append hprefix tailTrace_441151
  have hstable : (prefixWord ++ tailWord_441151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441151).length < 2 ^ (prefixWord ++ tailWord_441151).sum := by decide
  have hdescent : baseEnd_441151 < baseStart_441151 := by decide
  rcases family_descends (prefixWord ++ tailWord_441151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441168 : List Nat := [2, 1, 1, 1, 1, 4, 6, 1, 4]
def baseStart_441168 : Nat := 118140960795 + 441168 * 2 ^ 59
def prefixEnd_441168 : Nat := 4983230072969 + 3 ^ 40 * 441168 * 2
def baseEnd_441168 : Nat := 100680548170148960831605

theorem tailTrace_441168 : CollatzResearch.WordTrace tailWord_441168 prefixEnd_441168 100680548170148960831605 := by
  unfold tailWord_441168
  simp only [CollatzResearch.WordTrace]
  refine ⟨8045359432865578170474079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10727145910487437560632105 8045359432865578170474079)
  ·
    refine ⟨12068039149298367255711119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8045359432865578170474079 12068039149298367255711119)
    ·
      refine ⟨18102058723947550883566679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12068039149298367255711119 18102058723947550883566679)
      ·
        refine ⟨27153088085921326325350019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18102058723947550883566679 27153088085921326325350019)
        ·
          refine ⟨40729632128881989488025029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27153088085921326325350019 40729632128881989488025029)
          ·
            refine ⟨7636806024165373029004693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40729632128881989488025029 7636806024165373029004693)
            ·
              refine ⟨357975282382751860734595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7636806024165373029004693 357975282382751860734595)
              ·
                refine ⟨536962923574127791101893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357975282382751860734595 536962923574127791101893)
                ·
                  refine ⟨100680548170148960831605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 536962923574127791101893 100680548170148960831605)
                  ·
                    rfl

theorem cell21_441168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 4].length) (baseStart_441168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441168 prefixEnd_441168 := by exact prefixLift 441168
  have htrace : WordTrace (prefixWord ++ tailWord_441168) baseStart_441168 baseEnd_441168 := by
    simpa [prefixWord, tailWord_441168, baseEnd_441168] using wordTrace_append hprefix tailTrace_441168
  have hstable : (prefixWord ++ tailWord_441168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441168).length < 2 ^ (prefixWord ++ tailWord_441168).sum := by decide
  have hdescent : baseEnd_441168 < baseStart_441168 := by decide
  rcases family_descends (prefixWord ++ tailWord_441168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441227 : List Nat := [1, 1, 1, 1, 4, 2, 4, 3, 4]
def baseStart_441227 : Nat := 118140960795 + 441227 * 2 ^ 59
def prefixEnd_441227 : Nat := 4983230072969 + 3 ^ 40 * 441227 * 2
def baseEnd_441227 : Nat := 100694012773977969348151

theorem tailTrace_441227 : CollatzResearch.WordTrace tailWord_441227 prefixEnd_441227 100694012773977969348151 := by
  unfold tailWord_441227
  simp only [CollatzResearch.WordTrace]
  refine ⟨16092870772517409417345935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10728580515011606278230623 16092870772517409417345935)
  ·
    refine ⟨24139306158776114126018903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16092870772517409417345935 24139306158776114126018903)
    ·
      refine ⟨36208959238164171189028355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24139306158776114126018903 36208959238164171189028355)
      ·
        refine ⟨54313438857246256783542533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36208959238164171189028355 54313438857246256783542533)
        ·
          refine ⟨10183769785733673146914225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54313438857246256783542533 10183769785733673146914225)
          ·
            refine ⟨7637827339300254860185669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10183769785733673146914225 7637827339300254860185669)
            ·
              refine ⟨1432092626118797786284813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7637827339300254860185669 1432092626118797786284813)
              ·
                refine ⟨537034734794549169856805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1432092626118797786284813 537034734794549169856805)
                ·
                  refine ⟨100694012773977969348151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 537034734794549169856805 100694012773977969348151)
                  ·
                    rfl

theorem cell21_441227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 4].length) (baseStart_441227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441227 prefixEnd_441227 := by exact prefixLift 441227
  have htrace : WordTrace (prefixWord ++ tailWord_441227) baseStart_441227 baseEnd_441227 := by
    simpa [prefixWord, tailWord_441227, baseEnd_441227] using wordTrace_append hprefix tailTrace_441227
  have hstable : (prefixWord ++ tailWord_441227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441227).length < 2 ^ (prefixWord ++ tailWord_441227).sum := by decide
  have hdescent : baseEnd_441227 < baseStart_441227 := by decide
  rcases family_descends (prefixWord ++ tailWord_441227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441261 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 6]
def baseStart_441261 : Nat := 118140960795 + 441261 * 2 ^ 59
def prefixEnd_441261 : Nat := 4983230072969 + 3 ^ 40 * 441261 * 2
def baseEnd_441261 : Nat := 100701772037201465781415

theorem tailTrace_441261 : CollatzResearch.WordTrace tailWord_441261 prefixEnd_441261 100701772037201465781415 := by
  unfold tailWord_441261
  simp only [CollatzResearch.WordTrace]
  refine ⟨16094110854394233224083637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10729407236262822149389091 16094110854394233224083637)
  ·
    refine ⟨1508822892599459364757841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16094110854394233224083637 1508822892599459364757841)
    ·
      refine ⟨1131617169449594523568381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1508822892599459364757841 1131617169449594523568381)
      ·
        refine ⟨424356438543597946338143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1131617169449594523568381 424356438543597946338143)
        ·
          refine ⟨636534657815396919507215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424356438543597946338143 636534657815396919507215)
          ·
            refine ⟨954801986723095379260823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636534657815396919507215 954801986723095379260823)
            ·
              refine ⟨1432202980084643068891235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954801986723095379260823 1432202980084643068891235)
              ·
                refine ⟨2148304470126964603336853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432202980084643068891235 2148304470126964603336853)
                ·
                  refine ⟨100701772037201465781415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2148304470126964603336853 100701772037201465781415)
                  ·
                    rfl

theorem cell21_441261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_441261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441261 prefixEnd_441261 := by exact prefixLift 441261
  have htrace : WordTrace (prefixWord ++ tailWord_441261) baseStart_441261 baseEnd_441261 := by
    simpa [prefixWord, tailWord_441261, baseEnd_441261] using wordTrace_append hprefix tailTrace_441261
  have hstable : (prefixWord ++ tailWord_441261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441261).length < 2 ^ (prefixWord ++ tailWord_441261).sum := by decide
  have hdescent : baseEnd_441261 < baseStart_441261 := by decide
  rcases family_descends (prefixWord ++ tailWord_441261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441272 : List Nat := [2, 1, 2, 1, 2, 4, 1, 3, 5]
def baseStart_441272 : Nat := 118140960795 + 441272 * 2 ^ 59
def prefixEnd_441272 : Nat := 4983230072969 + 3 ^ 40 * 441272 * 2
def baseEnd_441272 : Nat := 100704282387067891098059

theorem tailTrace_441272 : CollatzResearch.WordTrace tailWord_441272 prefixEnd_441272 100704282387067891098059 := by
  unfold tailWord_441272
  simp only [CollatzResearch.WordTrace]
  refine ⟨8047256028677191051367035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10729674704902921401822713 8047256028677191051367035)
  ·
    refine ⟨12070884043015786577050553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8047256028677191051367035 12070884043015786577050553)
    ·
      refine ⟨9053163032261839932787915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12070884043015786577050553 9053163032261839932787915)
      ·
        refine ⟨13579744548392759899181873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9053163032261839932787915 13579744548392759899181873)
        ·
          refine ⟨10184808411294569924386405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13579744548392759899181873 10184808411294569924386405)
          ·
            refine ⟨1909651577117731860822451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10184808411294569924386405 1909651577117731860822451)
            ·
              refine ⟨2864477365676597791233677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909651577117731860822451 2864477365676597791233677)
              ·
                refine ⟨1074179012128724171712629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2864477365676597791233677 1074179012128724171712629)
                ·
                  refine ⟨100704282387067891098059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1074179012128724171712629 100704282387067891098059)
                  ·
                    rfl

theorem cell21_441272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_441272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441272 prefixEnd_441272 := by exact prefixLift 441272
  have htrace : WordTrace (prefixWord ++ tailWord_441272) baseStart_441272 baseEnd_441272 := by
    simpa [prefixWord, tailWord_441272, baseEnd_441272] using wordTrace_append hprefix tailTrace_441272
  have hstable : (prefixWord ++ tailWord_441272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441272).length < 2 ^ (prefixWord ++ tailWord_441272).sum := by decide
  have hdescent : baseEnd_441272 < baseStart_441272 := by decide
  rcases family_descends (prefixWord ++ tailWord_441272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441306 : List Nat := [3, 1, 1, 2, 4, 1, 3, 3, 3]
def baseStart_441306 : Nat := 118140960795 + 441306 * 2 ^ 59
def prefixEnd_441306 : Nat := 4983230072969 + 3 ^ 40 * 441306 * 2
def baseEnd_441306 : Nat := 100712041650291387531323

theorem tailTrace_441306 : CollatzResearch.WordTrace tailWord_441306 prefixEnd_441306 100712041650291387531323 := by
  unfold tailWord_441306
  simp only [CollatzResearch.WordTrace]
  refine ⟨4023938034807801477367943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10730501426154137272981181 4023938034807801477367943)
  ·
    refine ⟨6035907052211702216051915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4023938034807801477367943 6035907052211702216051915)
    ·
      refine ⟨9053860578317553324077873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6035907052211702216051915 9053860578317553324077873)
      ·
        refine ⟨6790395433738164993058405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9053860578317553324077873 6790395433738164993058405)
        ·
          refine ⟨1273199143825905936198451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6790395433738164993058405 1273199143825905936198451)
          ·
            refine ⟨1909798715738858904297677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273199143825905936198451 1909798715738858904297677)
            ·
              refine ⟨716174518402072089111629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1909798715738858904297677 716174518402072089111629)
              ·
                refine ⟨268565444400777033416861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 716174518402072089111629 268565444400777033416861)
                ·
                  refine ⟨100712041650291387531323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 268565444400777033416861 100712041650291387531323)
                  ·
                    rfl

theorem cell21_441306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_441306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441306 prefixEnd_441306 := by exact prefixLift 441306
  have htrace : WordTrace (prefixWord ++ tailWord_441306) baseStart_441306 baseEnd_441306 := by
    simpa [prefixWord, tailWord_441306, baseEnd_441306] using wordTrace_append hprefix tailTrace_441306
  have hstable : (prefixWord ++ tailWord_441306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441306).length < 2 ^ (prefixWord ++ tailWord_441306).sum := by decide
  have hdescent : baseEnd_441306 < baseStart_441306 := by decide
  rcases family_descends (prefixWord ++ tailWord_441306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441334 : List Nat := [5, 1, 1, 1, 3, 1, 1, 8]
def baseStart_441334 : Nat := 118140960795 + 441334 * 2 ^ 59
def prefixEnd_441334 : Nat := 4983230072969 + 3 ^ 40 * 441334 * 2
def baseEnd_441334 : Nat := 33572810543923187021533

theorem tailTrace_441334 : CollatzResearch.WordTrace tailWord_441334 prefixEnd_441334 33572810543923187021533 := by
  unfold tailWord_441334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1006048336445610418218191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10731182255419844460994037 1006048336445610418218191)
  ·
    refine ⟨1509072504668415627327287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1006048336445610418218191 1509072504668415627327287)
    ·
      refine ⟨2263608757002623440990931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1509072504668415627327287 2263608757002623440990931)
      ·
        refine ⟨3395413135503935161486397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2263608757002623440990931 3395413135503935161486397)
        ·
          refine ⟨1273279925813975685557399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3395413135503935161486397 1273279925813975685557399)
          ·
            refine ⟨1909919888720963528336099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273279925813975685557399 1909919888720963528336099)
            ·
              refine ⟨2864879833081445292504149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909919888720963528336099 2864879833081445292504149)
              ·
                refine ⟨33572810543923187021533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2864879833081445292504149 33572810543923187021533)
                ·
                  rfl

theorem cell21_441334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_441334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441334 prefixEnd_441334 := by exact prefixLift 441334
  have htrace : WordTrace (prefixWord ++ tailWord_441334) baseStart_441334 baseEnd_441334 := by
    simpa [prefixWord, tailWord_441334, baseEnd_441334] using wordTrace_append hprefix tailTrace_441334
  have hstable : (prefixWord ++ tailWord_441334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441334).length < 2 ^ (prefixWord ++ tailWord_441334).sum := by decide
  have hdescent : baseEnd_441334 < baseStart_441334 := by decide
  rcases family_descends (prefixWord ++ tailWord_441334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441379 : List Nat := [1, 1, 1, 4, 3, 2, 1, 4, 4]
def baseStart_441379 : Nat := 118140960795 + 441379 * 2 ^ 59
def prefixEnd_441379 : Nat := 4983230072969 + 3 ^ 40 * 441379 * 2
def baseEnd_441379 : Nat := 100728701244859482814507

theorem tailTrace_441379 : CollatzResearch.WordTrace tailWord_441379 prefixEnd_441379 100728701244859482814507 := by
  unfold tailWord_441379
  simp only [CollatzResearch.WordTrace]
  refine ⟨16098414667966739376879191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10732276445311159584586127 16098414667966739376879191)
  ·
    refine ⟨24147622001950109065318787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16098414667966739376879191 24147622001950109065318787)
    ·
      refine ⟨36221433002925163597978181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24147622001950109065318787 36221433002925163597978181)
      ·
        refine ⟨6791518688048468174620909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36221433002925163597978181 6791518688048468174620909)
        ·
          refine ⟨2546819508018175565482841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6791518688048468174620909 2546819508018175565482841)
          ·
            refine ⟨1910114631013631674112131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2546819508018175565482841 1910114631013631674112131)
            ·
              refine ⟨2865171946520447511168197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1910114631013631674112131 2865171946520447511168197)
              ·
                refine ⟨537219739972583908344037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2865171946520447511168197 537219739972583908344037)
                ·
                  refine ⟨100728701244859482814507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 537219739972583908344037 100728701244859482814507)
                  ·
                    rfl

theorem cell21_441379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 4].length) (baseStart_441379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441379 prefixEnd_441379 := by exact prefixLift 441379
  have htrace : WordTrace (prefixWord ++ tailWord_441379) baseStart_441379 baseEnd_441379 := by
    simpa [prefixWord, tailWord_441379, baseEnd_441379] using wordTrace_append hprefix tailTrace_441379
  have hstable : (prefixWord ++ tailWord_441379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441379).length < 2 ^ (prefixWord ++ tailWord_441379).sum := by decide
  have hdescent : baseEnd_441379 < baseStart_441379 := by decide
  rcases family_descends (prefixWord ++ tailWord_441379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441441 : List Nat := [1, 2, 3, 1, 1, 2, 4, 4, 3]
def baseStart_441441 : Nat := 118140960795 + 441441 * 2 ^ 59
def prefixEnd_441441 : Nat := 4983230072969 + 3 ^ 40 * 441441 * 2
def baseEnd_441441 : Nat := 100742850489561152781047

theorem tailTrace_441441 : CollatzResearch.WordTrace tailWord_441441 prefixEnd_441441 100742850489561152781047 := by
  unfold tailWord_441441
  simp only [CollatzResearch.WordTrace]
  refine ⟨16100675993742123965636177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10733783995828082643757451 16100675993742123965636177)
  ·
    refine ⟨12075506995306592974227133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16100675993742123965636177 12075506995306592974227133)
    ·
      refine ⟨4528315123239972365335175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12075506995306592974227133 4528315123239972365335175)
      ·
        refine ⟨6792472684859958548002763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4528315123239972365335175 6792472684859958548002763)
        ·
          refine ⟨10188709027289937822004145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6792472684859958548002763 10188709027289937822004145)
          ·
            refine ⟨7641531770467453366503109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10188709027289937822004145 7641531770467453366503109)
            ·
              refine ⟨1432787206962647506219333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7641531770467453366503109 1432787206962647506219333)
              ·
                refine ⟨268647601305496407416125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1432787206962647506219333 268647601305496407416125)
                ·
                  refine ⟨100742850489561152781047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 268647601305496407416125 100742850489561152781047)
                  ·
                    rfl

theorem cell21_441441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 3].length) (baseStart_441441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441441 prefixEnd_441441 := by exact prefixLift 441441
  have htrace : WordTrace (prefixWord ++ tailWord_441441) baseStart_441441 baseEnd_441441 := by
    simpa [prefixWord, tailWord_441441, baseEnd_441441] using wordTrace_append hprefix tailTrace_441441
  have hstable : (prefixWord ++ tailWord_441441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441441).length < 2 ^ (prefixWord ++ tailWord_441441).sum := by decide
  have hdescent : baseEnd_441441 < baseStart_441441 := by decide
  rcases family_descends (prefixWord ++ tailWord_441441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441461 : List Nat := [1, 3, 4, 3, 2, 1, 2, 5]
def baseStart_441461 : Nat := 118140960795 + 441461 * 2 ^ 59
def prefixEnd_441461 : Nat := 4983230072969 + 3 ^ 40 * 441461 * 2
def baseEnd_441461 : Nat := 33582471587348520815891

theorem tailTrace_441461 : CollatzResearch.WordTrace tailWord_441461 prefixEnd_441461 33582471587348520815891 := by
  unfold tailWord_441461
  simp only [CollatzResearch.WordTrace]
  refine ⟨16101405453669667381364237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10734270302446444920909491 16101405453669667381364237)
  ·
    refine ⟨6038027045126125268011589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16101405453669667381364237 6038027045126125268011589)
    ·
      refine ⟨1132130070961148487752173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6038027045126125268011589 1132130070961148487752173)
      ·
        refine ⟨424548776610430682907065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1132130070961148487752173 424548776610430682907065)
        ·
          refine ⟨318411582457823012180299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424548776610430682907065 318411582457823012180299)
          ·
            refine ⟨477617373686734518270449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318411582457823012180299 477617373686734518270449)
            ·
              refine ⟨358213030265050888702837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477617373686734518270449 358213030265050888702837)
              ·
                refine ⟨33582471587348520815891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 358213030265050888702837 33582471587348520815891)
                ·
                  rfl

theorem cell21_441461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 5].length) (baseStart_441461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441461 prefixEnd_441461 := by exact prefixLift 441461
  have htrace : WordTrace (prefixWord ++ tailWord_441461) baseStart_441461 baseEnd_441461 := by
    simpa [prefixWord, tailWord_441461, baseEnd_441461] using wordTrace_append hprefix tailTrace_441461
  have hstable : (prefixWord ++ tailWord_441461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441461).length < 2 ^ (prefixWord ++ tailWord_441461).sum := by decide
  have hdescent : baseEnd_441461 < baseStart_441461 := by decide
  rcases family_descends (prefixWord ++ tailWord_441461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441469 : List Nat := [1, 4, 1, 1, 3, 1, 3, 7]
def baseStart_441469 : Nat := 118140960795 + 441469 * 2 ^ 59
def prefixEnd_441469 : Nat := 4983230072969 + 3 ^ 40 * 441469 * 2
def baseEnd_441469 : Nat := 33583080157013108771441

theorem tailTrace_441469 : CollatzResearch.WordTrace tailWord_441469 prefixEnd_441469 33583080157013108771441 := by
  unfold tailWord_441469
  simp only [CollatzResearch.WordTrace]
  refine ⟨16101697237640684747655461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10734464825093789831770307 16101697237640684747655461)
  ·
    refine ⟨3019068232057628390185399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16101697237640684747655461 3019068232057628390185399)
    ·
      refine ⟨4528602348086442585278099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3019068232057628390185399 4528602348086442585278099)
      ·
        refine ⟨6792903522129663877917149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4528602348086442585278099 6792903522129663877917149)
        ·
          refine ⟨2547338820798623954218931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6792903522129663877917149 2547338820798623954218931)
          ·
            refine ⟨3821008231197935931328397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2547338820798623954218931 3821008231197935931328397)
            ·
              refine ⟨1432878086699225974248149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3821008231197935931328397 1432878086699225974248149)
              ·
                refine ⟨33583080157013108771441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1432878086699225974248149 33583080157013108771441)
                ·
                  rfl

theorem cell21_441469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 7].length) (baseStart_441469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441469 prefixEnd_441469 := by exact prefixLift 441469
  have htrace : WordTrace (prefixWord ++ tailWord_441469) baseStart_441469 baseEnd_441469 := by
    simpa [prefixWord, tailWord_441469, baseEnd_441469] using wordTrace_append hprefix tailTrace_441469
  have hstable : (prefixWord ++ tailWord_441469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441469).length < 2 ^ (prefixWord ++ tailWord_441469).sum := by decide
  have hdescent : baseEnd_441469 < baseStart_441469 := by decide
  rcases family_descends (prefixWord ++ tailWord_441469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441483 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 7]
def baseStart_441483 : Nat := 118140960795 + 441483 * 2 ^ 59
def prefixEnd_441483 : Nat := 4983230072969 + 3 ^ 40 * 441483 * 2
def baseEnd_441483 : Nat := 100752435461778413080961

theorem tailTrace_441483 : CollatzResearch.WordTrace tailWord_441483 prefixEnd_441483 100752435461778413080961 := by
  unfold tailWord_441483
  simp only [CollatzResearch.WordTrace]
  refine ⟨16102207859589965138665103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10734805239726643425776735 16102207859589965138665103)
  ·
    refine ⟨24153311789384947707997655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16102207859589965138665103 24153311789384947707997655)
    ·
      refine ⟨36229967684077421561996483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24153311789384947707997655 36229967684077421561996483)
      ·
        refine ⟨54344951526116132342994725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36229967684077421561996483 54344951526116132342994725)
        ·
          refine ⟨10189678411146774814311511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54344951526116132342994725 10189678411146774814311511)
          ·
            refine ⟨15284517616720162221467267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10189678411146774814311511 15284517616720162221467267)
            ·
              refine ⟨22926776425080243332200901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15284517616720162221467267 22926776425080243332200901)
              ·
                refine ⟨4298770579702545624787669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22926776425080243332200901 4298770579702545624787669)
                ·
                  refine ⟨100752435461778413080961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4298770579702545624787669 100752435461778413080961)
                  ·
                    rfl

theorem cell21_441483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 7].length) (baseStart_441483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441483 prefixEnd_441483 := by exact prefixLift 441483
  have htrace : WordTrace (prefixWord ++ tailWord_441483) baseStart_441483 baseEnd_441483 := by
    simpa [prefixWord, tailWord_441483, baseEnd_441483] using wordTrace_append hprefix tailTrace_441483
  have hstable : (prefixWord ++ tailWord_441483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441483).length < 2 ^ (prefixWord ++ tailWord_441483).sum := by decide
  have hdescent : baseEnd_441483 < baseStart_441483 := by decide
  rcases family_descends (prefixWord ++ tailWord_441483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441486 : List Nat := [4, 1, 1, 3, 2, 3, 7]
def baseStart_441486 : Nat := 118140960795 + 441486 * 2 ^ 59
def prefixEnd_441486 : Nat := 4983230072969 + 3 ^ 40 * 441486 * 2
def baseEnd_441486 : Nat := 11194791122516786058995

theorem tailTrace_441486 : CollatzResearch.WordTrace tailWord_441486 prefixEnd_441486 11194791122516786058995 := by
  unfold tailWord_441486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2012789659822387081378039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10734878185719397767349541 2012789659822387081378039)
  ·
    refine ⟨3019184489733580622067059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2012789659822387081378039 3019184489733580622067059)
    ·
      refine ⟨4528776734600370933100589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3019184489733580622067059 4528776734600370933100589)
      ·
        refine ⟨1698291275475139099912721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4528776734600370933100589 1698291275475139099912721)
        ·
          refine ⟨1273718456606354324934541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1698291275475139099912721 1273718456606354324934541)
          ·
            refine ⟨477644421227382871850453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1273718456606354324934541 477644421227382871850453)
            ·
              refine ⟨11194791122516786058995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 477644421227382871850453 11194791122516786058995)
              ·
                rfl

theorem cell21_441486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 7].length) (baseStart_441486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441486 prefixEnd_441486 := by exact prefixLift 441486
  have htrace : WordTrace (prefixWord ++ tailWord_441486) baseStart_441486 baseEnd_441486 := by
    simpa [prefixWord, tailWord_441486, baseEnd_441486] using wordTrace_append hprefix tailTrace_441486
  have hstable : (prefixWord ++ tailWord_441486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441486).length < 2 ^ (prefixWord ++ tailWord_441486).sum := by decide
  have hdescent : baseEnd_441486 < baseStart_441486 := by decide
  rcases family_descends (prefixWord ++ tailWord_441486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441506 : List Nat := [3, 3, 1, 3, 2, 2, 2, 1, 4]
def baseStart_441506 : Nat := 118140960795 + 441506 * 2 ^ 59
def prefixEnd_441506 : Nat := 4983230072969 + 3 ^ 40 * 441506 * 2
def baseEnd_441506 : Nat := 100757684375135484197581

theorem tailTrace_441506 : CollatzResearch.WordTrace tailWord_441506 prefixEnd_441506 100757684375135484197581 := by
  unfold tailWord_441506
  simp only [CollatzResearch.WordTrace]
  refine ⟨4025761684626660016688093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10735364492337760044501581 4025761684626660016688093)
  ·
    refine ⟨1509660631734997506258035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4025761684626660016688093 1509660631734997506258035)
    ·
      refine ⟨2264490947602496259387053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1509660631734997506258035 2264490947602496259387053)
      ·
        refine ⟨849184105350936097270145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2264490947602496259387053 849184105350936097270145)
        ·
          refine ⟨636888079013202072952609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 849184105350936097270145 636888079013202072952609)
          ·
            refine ⟨477666059259901554714457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 636888079013202072952609 477666059259901554714457)
            ·
              refine ⟨358249544444926166035843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477666059259901554714457 358249544444926166035843)
              ·
                refine ⟨537374316667389249053765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358249544444926166035843 537374316667389249053765)
                ·
                  refine ⟨100757684375135484197581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 537374316667389249053765 100757684375135484197581)
                  ·
                    rfl

theorem cell21_441506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_441506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441506 prefixEnd_441506 := by exact prefixLift 441506
  have htrace : WordTrace (prefixWord ++ tailWord_441506) baseStart_441506 baseEnd_441506 := by
    simpa [prefixWord, tailWord_441506, baseEnd_441506] using wordTrace_append hprefix tailTrace_441506
  have hstable : (prefixWord ++ tailWord_441506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441506).length < 2 ^ (prefixWord ++ tailWord_441506).sum := by decide
  have hdescent : baseEnd_441506 < baseStart_441506 := by decide
  rcases family_descends (prefixWord ++ tailWord_441506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441576 : List Nat := [2, 1, 4, 1, 2, 1, 3, 2, 5]
def baseStart_441576 : Nat := 118140960795 + 441576 * 2 ^ 59
def prefixEnd_441576 : Nat := 4983230072969 + 3 ^ 40 * 441576 * 2
def baseEnd_441576 : Nat := 100773659328830918030771

theorem tailTrace_441576 : CollatzResearch.WordTrace tailWord_441576 prefixEnd_441576 100773659328830918030771 := by
  unfold tailWord_441576
  simp only [CollatzResearch.WordTrace]
  refine ⟨8052799924126521010900291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10737066565502028014533721 8052799924126521010900291)
  ·
    refine ⟨12079199886189781516350437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8052799924126521010900291 12079199886189781516350437)
    ·
      refine ⟨2264849978660584034315707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12079199886189781516350437 2264849978660584034315707)
      ·
        refine ⟨3397274967990876051473561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2264849978660584034315707 3397274967990876051473561)
        ·
          refine ⟨2547956225993157038605171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3397274967990876051473561 2547956225993157038605171)
          ·
            refine ⟨3821934338989735557907757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2547956225993157038605171 3821934338989735557907757)
            ·
              refine ⟨1433225377121150834215409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3821934338989735557907757 1433225377121150834215409)
              ·
                refine ⟨1074919032840863125661557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1433225377121150834215409 1074919032840863125661557)
                ·
                  refine ⟨100773659328830918030771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1074919032840863125661557 100773659328830918030771)
                  ·
                    rfl

theorem cell21_441576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_441576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441576 prefixEnd_441576 := by exact prefixLift 441576
  have htrace : WordTrace (prefixWord ++ tailWord_441576) baseStart_441576 baseEnd_441576 := by
    simpa [prefixWord, tailWord_441576, baseEnd_441576] using wordTrace_append hprefix tailTrace_441576
  have hstable : (prefixWord ++ tailWord_441576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441576).length < 2 ^ (prefixWord ++ tailWord_441576).sum := by decide
  have hdescent : baseEnd_441576 < baseStart_441576 := by decide
  rcases family_descends (prefixWord ++ tailWord_441576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441593 : List Nat := [1, 2, 1, 3, 1, 1, 6, 3, 3]
def baseStart_441593 : Nat := 118140960795 + 441593 * 2 ^ 59
def prefixEnd_441593 : Nat := 4983230072969 + 3 ^ 40 * 441593 * 2
def baseEnd_441593 : Nat := 100777538960442666247403

theorem tailTrace_441593 : CollatzResearch.WordTrace tailWord_441593 prefixEnd_441593 100777538960442666247403 := by
  unfold tailWord_441593
  simp only [CollatzResearch.WordTrace]
  refine ⟨16106219889191453925169433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10737479926127635950112955 16106219889191453925169433)
  ·
    refine ⟨12079664916893590443877075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16106219889191453925169433 12079664916893590443877075)
    ·
      refine ⟨18119497375340385665815613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12079664916893590443877075 18119497375340385665815613)
      ·
        refine ⟨6794811515752644624680855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18119497375340385665815613 6794811515752644624680855)
        ·
          refine ⟨10192217273628966937021283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6794811515752644624680855 10192217273628966937021283)
          ·
            refine ⟨15288325910443450405531925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10192217273628966937021283 15288325910443450405531925)
            ·
              refine ⟨716640277052036737759309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15288325910443450405531925 716640277052036737759309)
              ·
                refine ⟨268740103894513776659741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 716640277052036737759309 268740103894513776659741)
                ·
                  refine ⟨100777538960442666247403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 268740103894513776659741 100777538960442666247403)
                  ·
                    rfl

theorem cell21_441593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 3].length) (baseStart_441593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441593 prefixEnd_441593 := by exact prefixLift 441593
  have htrace : WordTrace (prefixWord ++ tailWord_441593) baseStart_441593 baseEnd_441593 := by
    simpa [prefixWord, tailWord_441593, baseEnd_441593] using wordTrace_append hprefix tailTrace_441593
  have hstable : (prefixWord ++ tailWord_441593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441593).length < 2 ^ (prefixWord ++ tailWord_441593).sum := by decide
  have hdescent : baseEnd_441593 < baseStart_441593 := by decide
  rcases family_descends (prefixWord ++ tailWord_441593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441624 : List Nat := [2, 1, 2, 3, 1, 4, 3, 1, 4]
def baseStart_441624 : Nat := 118140960795 + 441624 * 2 ^ 59
def prefixEnd_441624 : Nat := 4983230072969 + 3 ^ 40 * 441624 * 2
def baseEnd_441624 : Nat := 100784613582793501230673

theorem tailTrace_441624 : CollatzResearch.WordTrace tailWord_441624 prefixEnd_441624 100784613582793501230673 := by
  unfold tailWord_441624
  simp only [CollatzResearch.WordTrace]
  refine ⟨8053675276039573109773963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10738233701386097479698617 8053675276039573109773963)
  ·
    refine ⟨12080512914059359664660945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8053675276039573109773963 12080512914059359664660945)
    ·
      refine ⟨9060384685544519748495709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12080512914059359664660945 9060384685544519748495709)
      ·
        refine ⟨3397644257079194905685891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9060384685544519748495709 3397644257079194905685891)
        ·
          refine ⟨5096466385618792358528837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3397644257079194905685891 5096466385618792358528837)
          ·
            refine ⟨955587447303523567224157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5096466385618792358528837 955587447303523567224157)
            ·
              refine ⟨358345292738821337709059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 955587447303523567224157 358345292738821337709059)
              ·
                refine ⟨537517939108232006563589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358345292738821337709059 537517939108232006563589)
                ·
                  refine ⟨100784613582793501230673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 537517939108232006563589 100784613582793501230673)
                  ·
                    rfl

theorem cell21_441624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 4].length) (baseStart_441624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441624 prefixEnd_441624 := by exact prefixLift 441624
  have htrace : WordTrace (prefixWord ++ tailWord_441624) baseStart_441624 baseEnd_441624 := by
    simpa [prefixWord, tailWord_441624, baseEnd_441624] using wordTrace_append hprefix tailTrace_441624
  have hstable : (prefixWord ++ tailWord_441624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441624).length < 2 ^ (prefixWord ++ tailWord_441624).sum := by decide
  have hdescent : baseEnd_441624 < baseStart_441624 := by decide
  rcases family_descends (prefixWord ++ tailWord_441624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441762 : List Nat := [3, 3, 1, 2, 1, 3, 2, 3, 3]
def baseStart_441762 : Nat := 118140960795 + 441762 * 2 ^ 59
def prefixEnd_441762 : Nat := 4983230072969 + 3 ^ 40 * 441762 * 2
def baseEnd_441762 : Nat := 100816107062935927930391

theorem tailTrace_441762 : CollatzResearch.WordTrace tailWord_441762 prefixEnd_441762 100816107062935927930391 := by
  unfold tailWord_441762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4028095956394798947017885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10741589217052797192047693 4028095956394798947017885)
  ·
    refine ⟨1510535983648049605131707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4028095956394798947017885 1510535983648049605131707)
    ·
      refine ⟨2265803975472074407697561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1510535983648049605131707 2265803975472074407697561)
      ·
        refine ⟨1699352981604055805773171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2265803975472074407697561 1699352981604055805773171)
        ·
          refine ⟨2549029472406083708659757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1699352981604055805773171 2549029472406083708659757)
          ·
            refine ⟨955886052152281390747409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2549029472406083708659757 955886052152281390747409)
            ·
              refine ⟨716914539114211043060557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 955886052152281390747409 716914539114211043060557)
              ·
                refine ⟨268842952167829141147709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 716914539114211043060557 268842952167829141147709)
                ·
                  refine ⟨100816107062935927930391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 268842952167829141147709 100816107062935927930391)
                  ·
                    rfl

theorem cell21_441762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_441762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441762 prefixEnd_441762 := by exact prefixLift 441762
  have htrace : WordTrace (prefixWord ++ tailWord_441762) baseStart_441762 baseEnd_441762 := by
    simpa [prefixWord, tailWord_441762, baseEnd_441762] using wordTrace_append hprefix tailTrace_441762
  have hstable : (prefixWord ++ tailWord_441762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441762).length < 2 ^ (prefixWord ++ tailWord_441762).sum := by decide
  have hdescent : baseEnd_441762 < baseStart_441762 := by decide
  rcases family_descends (prefixWord ++ tailWord_441762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441804 : List Nat := [2, 2, 1, 4, 2, 1, 2, 2, 5]
def baseStart_441804 : Nat := 118140960795 + 441804 * 2 ^ 59
def prefixEnd_441804 : Nat := 4983230072969 + 3 ^ 40 * 441804 * 2
def baseEnd_441804 : Nat := 100825692035153188230305

theorem tailTrace_441804 : CollatzResearch.WordTrace tailWord_441804 prefixEnd_441804 100825692035153188230305 := by
  unfold tailWord_441804
  simp only [CollatzResearch.WordTrace]
  refine ⟨8056957845713518480550233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10742610460951357974066977 8056957845713518480550233)
  ·
    refine ⟨6042718384285138860412675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8056957845713518480550233 6042718384285138860412675)
    ·
      refine ⟨9064077576427708290619013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6042718384285138860412675 9064077576427708290619013)
      ·
        refine ⟨1699514545580195304491065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9064077576427708290619013 1699514545580195304491065)
        ·
          refine ⟨1274635909185146478368299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1699514545580195304491065 1274635909185146478368299)
          ·
            refine ⟨1911953863777719717552449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274635909185146478368299 1911953863777719717552449)
            ·
              refine ⟨1433965397833289788164337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1911953863777719717552449 1433965397833289788164337)
              ·
                refine ⟨1075474048374967341123253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1433965397833289788164337 1075474048374967341123253)
                ·
                  refine ⟨100825692035153188230305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1075474048374967341123253 100825692035153188230305)
                  ·
                    rfl

theorem cell21_441804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_441804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441804 prefixEnd_441804 := by exact prefixLift 441804
  have htrace : WordTrace (prefixWord ++ tailWord_441804) baseStart_441804 baseEnd_441804 := by
    simpa [prefixWord, tailWord_441804, baseEnd_441804] using wordTrace_append hprefix tailTrace_441804
  have hstable : (prefixWord ++ tailWord_441804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441804).length < 2 ^ (prefixWord ++ tailWord_441804).sum := by decide
  have hdescent : baseEnd_441804 < baseStart_441804 := by decide
  rcases family_descends (prefixWord ++ tailWord_441804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441818 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 6]
def baseStart_441818 : Nat := 118140960795 + 441818 * 2 ^ 59
def prefixEnd_441818 : Nat := 4983230072969 + 3 ^ 40 * 441818 * 2
def baseEnd_441818 : Nat := 100828887025892274996943

theorem tailTrace_441818 : CollatzResearch.WordTrace tailWord_441818 prefixEnd_441818 100828887025892274996943 := by
  unfold tailWord_441818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4028606578344079338027527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10742950875584211568073405 4028606578344079338027527)
  ·
    refine ⟨6042909867516119007041291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4028606578344079338027527 6042909867516119007041291)
    ·
      refine ⟨9064364801274178510561937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6042909867516119007041291 9064364801274178510561937)
      ·
        refine ⟨6798273600955633882921453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9064364801274178510561937 6798273600955633882921453)
        ·
          refine ⟨2549352600358362706095545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6798273600955633882921453 2549352600358362706095545)
          ·
            refine ⟨1912014450268772029571659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2549352600358362706095545 1912014450268772029571659)
            ·
              refine ⟨2868021675403158044357489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1912014450268772029571659 2868021675403158044357489)
              ·
                refine ⟨2151016256552368533268117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2868021675403158044357489 2151016256552368533268117)
                ·
                  refine ⟨100828887025892274996943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2151016256552368533268117 100828887025892274996943)
                  ·
                    rfl

theorem cell21_441818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_441818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441818 prefixEnd_441818 := by exact prefixLift 441818
  have htrace : WordTrace (prefixWord ++ tailWord_441818) baseStart_441818 baseEnd_441818 := by
    simpa [prefixWord, tailWord_441818, baseEnd_441818] using wordTrace_append hprefix tailTrace_441818
  have hstable : (prefixWord ++ tailWord_441818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441818).length < 2 ^ (prefixWord ++ tailWord_441818).sum := by decide
  have hdescent : baseEnd_441818 < baseStart_441818 := by decide
  rcases family_descends (prefixWord ++ tailWord_441818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441838 : List Nat := [4, 1, 2, 1, 2, 1, 5, 2, 3]
def baseStart_441838 : Nat := 118140960795 + 441838 * 2 ^ 59
def prefixEnd_441838 : Nat := 4983230072969 + 3 ^ 40 * 441838 * 2
def baseEnd_441838 : Nat := 100833451298376684663569

theorem tailTrace_441838 : CollatzResearch.WordTrace tailWord_441838 prefixEnd_441838 100833451298376684663569 := by
  unfold tailWord_441838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2014394471662982595979771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10743437182202573845225445 2014394471662982595979771)
  ·
    refine ⟨3021591707494473893969657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2014394471662982595979771 3021591707494473893969657)
    ·
      refine ⟨2266193780620855420477243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3021591707494473893969657 2266193780620855420477243)
      ·
        refine ⟨3399290670931283130715865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2266193780620855420477243 3399290670931283130715865)
        ·
          refine ⟨2549468003198462348036899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3399290670931283130715865 2549468003198462348036899)
          ·
            refine ⟨3824202004797693522055349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549468003198462348036899 3824202004797693522055349)
            ·
              refine ⟨358518937949783767692689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3824202004797693522055349 358518937949783767692689)
              ·
                refine ⟨268889203462337825769517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 358518937949783767692689 268889203462337825769517)
                ·
                  refine ⟨100833451298376684663569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 268889203462337825769517 100833451298376684663569)
                  ·
                    rfl

theorem cell21_441838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_441838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441838 prefixEnd_441838 := by exact prefixLift 441838
  have htrace : WordTrace (prefixWord ++ tailWord_441838) baseStart_441838 baseEnd_441838 := by
    simpa [prefixWord, tailWord_441838, baseEnd_441838] using wordTrace_append hprefix tailTrace_441838
  have hstable : (prefixWord ++ tailWord_441838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441838).length < 2 ^ (prefixWord ++ tailWord_441838).sum := by decide
  have hdescent : baseEnd_441838 < baseStart_441838 := by decide
  rcases family_descends (prefixWord ++ tailWord_441838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441925 : List Nat := [1, 3, 1, 1, 1, 4, 5, 5]
def baseStart_441925 : Nat := 118140960795 + 441925 * 2 ^ 59
def prefixEnd_441925 : Nat := 4983230072969 + 3 ^ 40 * 441925 * 2
def baseEnd_441925 : Nat := 33617768627894622237797

theorem tailTrace_441925 : CollatzResearch.WordTrace tailWord_441925 prefixEnd_441925 33617768627894622237797 := by
  unfold tailWord_441925
  simp only [CollatzResearch.WordTrace]
  refine ⟨16118328923988674626255229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10745552615992449750836819 16118328923988674626255229)
  ·
    refine ⟨6044373346495752984845711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16118328923988674626255229 6044373346495752984845711)
    ·
      refine ⟨9066560019743629477268567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6044373346495752984845711 9066560019743629477268567)
      ·
        refine ⟨13599840029615444215902851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9066560019743629477268567 13599840029615444215902851)
        ·
          refine ⟨20399760044423166323854277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13599840029615444215902851 20399760044423166323854277)
          ·
            refine ⟨3824955008329343685722677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20399760044423166323854277 3824955008329343685722677)
            ·
              refine ⟨358589532030875970536501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3824955008329343685722677 358589532030875970536501)
              ·
                refine ⟨33617768627894622237797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 358589532030875970536501 33617768627894622237797)
                ·
                  rfl

theorem cell21_441925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 5].length) (baseStart_441925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441925 prefixEnd_441925 := by exact prefixLift 441925
  have htrace : WordTrace (prefixWord ++ tailWord_441925) baseStart_441925 baseEnd_441925 := by
    simpa [prefixWord, tailWord_441925, baseEnd_441925] using wordTrace_append hprefix tailTrace_441925
  have hstable : (prefixWord ++ tailWord_441925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441925).length < 2 ^ (prefixWord ++ tailWord_441925).sum := by decide
  have hdescent : baseEnd_441925 < baseStart_441925 := by decide
  rcases family_descends (prefixWord ++ tailWord_441925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441956 : List Nat := [2, 3, 1, 1, 2, 4, 2, 1, 5]
def baseStart_441956 : Nat := 118140960795 + 441956 * 2 ^ 59
def prefixEnd_441956 : Nat := 4983230072969 + 3 ^ 40 * 441956 * 2
def baseEnd_441956 : Nat := 100860380506034701696661

theorem tailTrace_441956 : CollatzResearch.WordTrace tailWord_441956 prefixEnd_441956 100860380506034701696661 := by
  unfold tailWord_441956
  simp only [CollatzResearch.WordTrace]
  refine ⟨8059729793438183460316861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10746306391250911280422481 8059729793438183460316861)
  ·
    refine ⟨3022398672539318797618823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8059729793438183460316861 3022398672539318797618823)
    ·
      refine ⟨4533598008808978196428235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3022398672539318797618823 4533598008808978196428235)
      ·
        refine ⟨6800397013213467294642353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4533598008808978196428235 6800397013213467294642353)
        ·
          refine ⟨5100297759910100470981765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6800397013213467294642353 5100297759910100470981765)
          ·
            refine ⟨956305829983143838309081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5100297759910100470981765 956305829983143838309081)
            ·
              refine ⟨717229372487357878731811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956305829983143838309081 717229372487357878731811)
              ·
                refine ⟨1075844058731036818097717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717229372487357878731811 1075844058731036818097717)
                ·
                  refine ⟨100860380506034701696661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1075844058731036818097717 100860380506034701696661)
                  ·
                    rfl

theorem cell21_441956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_441956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441956 prefixEnd_441956 := by exact prefixLift 441956
  have htrace : WordTrace (prefixWord ++ tailWord_441956) baseStart_441956 baseEnd_441956 := by
    simpa [prefixWord, tailWord_441956, baseEnd_441956] using wordTrace_append hprefix tailTrace_441956
  have hstable : (prefixWord ++ tailWord_441956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441956).length < 2 ^ (prefixWord ++ tailWord_441956).sum := by decide
  have hdescent : baseEnd_441956 < baseStart_441956 := by decide
  rcases family_descends (prefixWord ++ tailWord_441956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441984 : List Nat := [2, 1, 1, 2, 1, 4, 3, 7]
def baseStart_441984 : Nat := 118140960795 + 441984 * 2 ^ 59
def prefixEnd_441984 : Nat := 4983230072969 + 3 ^ 40 * 441984 * 2
def baseEnd_441984 : Nat := 33622256829170958409979

theorem tailTrace_441984 : CollatzResearch.WordTrace tailWord_441984 prefixEnd_441984 33622256829170958409979 := by
  unfold tailWord_441984
  simp only [CollatzResearch.WordTrace]
  refine ⟨8060240415387463851326503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10746987220516618468435337 8060240415387463851326503)
  ·
    refine ⟨12090360623081195776989755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8060240415387463851326503 12090360623081195776989755)
    ·
      refine ⟨18135540934621793665484633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12090360623081195776989755 18135540934621793665484633)
      ·
        refine ⟨13601655700966345249113475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18135540934621793665484633 13601655700966345249113475)
        ·
          refine ⟨20402483551449517873670213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13601655700966345249113475 20402483551449517873670213)
          ·
            refine ⟨3825465665896784601313165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20402483551449517873670213 3825465665896784601313165)
            ·
              refine ⟨1434549624711294225492437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3825465665896784601313165 1434549624711294225492437)
              ·
                refine ⟨33622256829170958409979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1434549624711294225492437 33622256829170958409979)
                ·
                  rfl

theorem cell21_441984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 7].length) (baseStart_441984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_441984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_441984 prefixEnd_441984 := by exact prefixLift 441984
  have htrace : WordTrace (prefixWord ++ tailWord_441984) baseStart_441984 baseEnd_441984 := by
    simpa [prefixWord, tailWord_441984, baseEnd_441984] using wordTrace_append hprefix tailTrace_441984
  have hstable : (prefixWord ++ tailWord_441984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441984).length < 2 ^ (prefixWord ++ tailWord_441984).sum := by decide
  have hdescent : baseEnd_441984 < baseStart_441984 := by decide
  rcases family_descends (prefixWord ++ tailWord_441984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442060 : List Nat := [2, 2, 1, 5, 11]
def baseStart_442060 : Nat := 118140960795 + 442060 * 2 ^ 59
def prefixEnd_442060 : Nat := 4983230072969 + 3 ^ 40 * 442060 * 2
def baseEnd_442060 : Nat := 1245482897814242369915

theorem tailTrace_442060 : CollatzResearch.WordTrace tailWord_442060 prefixEnd_442060 1245482897814242369915 := by
  unfold tailWord_442060
  simp only [CollatzResearch.WordTrace]
  refine ⟨8061626389249796341209817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10748835185666395121613089 8061626389249796341209817)
  ·
    refine ⟨6046219791937347255907363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8061626389249796341209817 6046219791937347255907363)
    ·
      refine ⟨9069329687906020883861045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6046219791937347255907363 9069329687906020883861045)
      ·
        refine ⟨850249658241189457861973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9069329687906020883861045 850249658241189457861973)
        ·
          refine ⟨1245482897814242369915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 850249658241189457861973 1245482897814242369915)
          ·
            rfl

theorem cell21_442060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 11].length) (baseStart_442060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442060 prefixEnd_442060 := by exact prefixLift 442060
  have htrace : WordTrace (prefixWord ++ tailWord_442060) baseStart_442060 baseEnd_442060 := by
    simpa [prefixWord, tailWord_442060, baseEnd_442060] using wordTrace_append hprefix tailTrace_442060
  have hstable : (prefixWord ++ tailWord_442060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442060).length < 2 ^ (prefixWord ++ tailWord_442060).sum := by decide
  have hdescent : baseEnd_442060 < baseStart_442060 := by decide
  rcases family_descends (prefixWord ++ tailWord_442060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442066 : List Nat := [3, 2, 2, 2, 2, 1, 4, 2, 3]
def baseStart_442066 : Nat := 118140960795 + 442066 * 2 ^ 59
def prefixEnd_442066 : Nat := 4983230072969 + 3 ^ 40 * 442066 * 2
def baseEnd_442066 : Nat := 100885484004698954863103

theorem tailTrace_442066 : CollatzResearch.WordTrace tailWord_442066 prefixEnd_442066 100885484004698954863103 := by
  unfold tailWord_442066
  simp only [CollatzResearch.WordTrace]
  refine ⟨4030867904119463926784513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10748981077651903804758701 4030867904119463926784513)
  ·
    refine ⟨3023150928089597945088385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4030867904119463926784513 3023150928089597945088385)
    ·
      refine ⟨2267363196067198458816289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3023150928089597945088385 2267363196067198458816289)
      ·
        refine ⟨1700522397050398844112217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2267363196067198458816289 1700522397050398844112217)
        ·
          refine ⟨1275391797787799133084163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1700522397050398844112217 1275391797787799133084163)
          ·
            refine ⟨1913087696681698699626245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275391797787799133084163 1913087696681698699626245)
            ·
              refine ⟨358703943127818506179921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1913087696681698699626245 358703943127818506179921)
              ·
                refine ⟨269027957345863879634941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 358703943127818506179921 269027957345863879634941)
                ·
                  refine ⟨100885484004698954863103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269027957345863879634941 100885484004698954863103)
                  ·
                    rfl

theorem cell21_442066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_442066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442066 prefixEnd_442066 := by exact prefixLift 442066
  have htrace : WordTrace (prefixWord ++ tailWord_442066) baseStart_442066 baseEnd_442066 := by
    simpa [prefixWord, tailWord_442066, baseEnd_442066] using wordTrace_append hprefix tailTrace_442066
  have hstable : (prefixWord ++ tailWord_442066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442066).length < 2 ^ (prefixWord ++ tailWord_442066).sum := by decide
  have hdescent : baseEnd_442066 < baseStart_442066 := by decide
  rcases family_descends (prefixWord ++ tailWord_442066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442122 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 6]
def baseStart_442122 : Nat := 118140960795 + 442122 * 2 ^ 59
def prefixEnd_442122 : Nat := 4983230072969 + 3 ^ 40 * 442122 * 2
def baseEnd_442122 : Nat := 100898263967655301929655

theorem tailTrace_442122 : CollatzResearch.WordTrace tailWord_442122 prefixEnd_442122 100898263967655301929655 := by
  unfold tailWord_442122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4031378526068744317794155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10750342736183318180784413 4031378526068744317794155)
  ·
    refine ⟨6047067789103116476691233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4031378526068744317794155 6047067789103116476691233)
    ·
      refine ⟨4535300841827337357518425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6047067789103116476691233 4535300841827337357518425)
      ·
        refine ⟨3401475631370503018138819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4535300841827337357518425 3401475631370503018138819)
        ·
          refine ⟨5102213447055754527208229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3401475631370503018138819 5102213447055754527208229)
          ·
            refine ⟨956665021322953973851543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5102213447055754527208229 956665021322953973851543)
            ·
              refine ⟨1434997531984430960777315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956665021322953973851543 1434997531984430960777315)
              ·
                refine ⟨2152496297976646441165973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1434997531984430960777315 2152496297976646441165973)
                ·
                  refine ⟨100898263967655301929655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2152496297976646441165973 100898263967655301929655)
                  ·
                    rfl

theorem cell21_442122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_442122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442122 prefixEnd_442122 := by exact prefixLift 442122
  have htrace : WordTrace (prefixWord ++ tailWord_442122) baseStart_442122 baseEnd_442122 := by
    simpa [prefixWord, tailWord_442122, baseEnd_442122] using wordTrace_append hprefix tailTrace_442122
  have hstable : (prefixWord ++ tailWord_442122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442122).length < 2 ^ (prefixWord ++ tailWord_442122).sum := by decide
  have hdescent : baseEnd_442122 < baseStart_442122 := by decide
  rcases family_descends (prefixWord ++ tailWord_442122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442181 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 6]
def baseStart_442181 : Nat := 118140960795 + 442181 * 2 ^ 59
def prefixEnd_442181 : Nat := 4983230072969 + 3 ^ 40 * 442181 * 2
def baseEnd_442181 : Nat := 100911728571484310446201

theorem tailTrace_442181 : CollatzResearch.WordTrace tailWord_442181 prefixEnd_442181 100911728571484310446201 := by
  unfold tailWord_442181
  simp only [CollatzResearch.WordTrace]
  refine ⟨16127666011061230347574397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10751777340707486898382931 16127666011061230347574397)
  ·
    refine ⟨6047874754147961380340399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16127666011061230347574397 6047874754147961380340399)
    ·
      refine ⟨9071812131221942070510599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6047874754147961380340399 9071812131221942070510599)
      ·
        refine ⟨13607718196832913105765899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9071812131221942070510599 13607718196832913105765899)
        ·
          refine ⟨20411577295249369658648849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13607718196832913105765899 20411577295249369658648849)
          ·
            refine ⟨15308682971437027243986637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20411577295249369658648849 15308682971437027243986637)
            ·
              refine ⟨5740756114288885216494989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15308682971437027243986637 5740756114288885216494989)
              ·
                refine ⟨2152783542858331956185621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5740756114288885216494989 2152783542858331956185621)
                ·
                  refine ⟨100911728571484310446201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2152783542858331956185621 100911728571484310446201)
                  ·
                    rfl

theorem cell21_442181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_442181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442181 prefixEnd_442181 := by exact prefixLift 442181
  have htrace : WordTrace (prefixWord ++ tailWord_442181) baseStart_442181 baseEnd_442181 := by
    simpa [prefixWord, tailWord_442181, baseEnd_442181] using wordTrace_append hprefix tailTrace_442181
  have hstable : (prefixWord ++ tailWord_442181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442181).length < 2 ^ (prefixWord ++ tailWord_442181).sum := by decide
  have hdescent : baseEnd_442181 < baseStart_442181 := by decide
  rcases family_descends (prefixWord ++ tailWord_442181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442184 : List Nat := [2, 1, 3, 1, 1, 6, 1, 1, 5]
def baseStart_442184 : Nat := 118140960795 + 442184 * 2 ^ 59
def prefixEnd_442184 : Nat := 4983230072969 + 3 ^ 40 * 442184 * 2
def baseEnd_442184 : Nat := 100912413212356971896195

theorem tailTrace_442184 : CollatzResearch.WordTrace tailWord_442184 prefixEnd_442184 100912413212356971896195 := by
  unfold tailWord_442184
  simp only [CollatzResearch.WordTrace]
  refine ⟨8063887715025180929966803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10751850286700241239955737 8063887715025180929966803)
  ·
    refine ⟨12095831572537771394950205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8063887715025180929966803 12095831572537771394950205)
    ·
      refine ⟨4535936839701664273106327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12095831572537771394950205 4535936839701664273106327)
      ·
        refine ⟨6803905259552496409659491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4535936839701664273106327 6803905259552496409659491)
        ·
          refine ⟨10205857889328744614489237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6803905259552496409659491 10205857889328744614489237)
          ·
            refine ⟨478399588562284903804183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10205857889328744614489237 478399588562284903804183)
            ·
              refine ⟨717599382843427355706275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478399588562284903804183 717599382843427355706275)
              ·
                refine ⟨1076399074265141033559413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717599382843427355706275 1076399074265141033559413)
                ·
                  refine ⟨100912413212356971896195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1076399074265141033559413 100912413212356971896195)
                  ·
                    rfl

theorem cell21_442184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 5].length) (baseStart_442184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442184 prefixEnd_442184 := by exact prefixLift 442184
  have htrace : WordTrace (prefixWord ++ tailWord_442184) baseStart_442184 baseEnd_442184 := by
    simpa [prefixWord, tailWord_442184, baseEnd_442184] using wordTrace_append hprefix tailTrace_442184
  have hstable : (prefixWord ++ tailWord_442184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442184).length < 2 ^ (prefixWord ++ tailWord_442184).sum := by decide
  have hdescent : baseEnd_442184 < baseStart_442184 := by decide
  rcases family_descends (prefixWord ++ tailWord_442184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442260 : List Nat := [2, 4, 2, 1, 1, 3, 1, 2, 5]
def baseStart_442260 : Nat := 118140960795 + 442260 * 2 ^ 59
def prefixEnd_442260 : Nat := 4983230072969 + 3 ^ 40 * 442260 * 2
def baseEnd_442260 : Nat := 100929757447797728629373

theorem tailTrace_442260 : CollatzResearch.WordTrace tailWord_442260 prefixEnd_442260 100929757447797728629373 := by
  unfold tailWord_442260
  simp only [CollatzResearch.WordTrace]
  refine ⟨8065273688887513419850117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10753698251850017893133489 8065273688887513419850117)
  ·
    refine ⟨1512238816666408766221897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8065273688887513419850117 1512238816666408766221897)
    ·
      refine ⟨1134179112499806574666423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1512238816666408766221897 1134179112499806574666423)
      ·
        refine ⟨1701268668749709861999635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134179112499806574666423 1701268668749709861999635)
        ·
          refine ⟨2551903003124564792999453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1701268668749709861999635 2551903003124564792999453)
          ·
            refine ⟨956963626171711797374795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2551903003124564792999453 956963626171711797374795)
            ·
              refine ⟨1435445439257567696062193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956963626171711797374795 1435445439257567696062193)
              ·
                refine ⟨1076584079443175772046645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1435445439257567696062193 1076584079443175772046645)
                ·
                  refine ⟨100929757447797728629373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1076584079443175772046645 100929757447797728629373)
                  ·
                    rfl

theorem cell21_442260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_442260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442260 prefixEnd_442260 := by exact prefixLift 442260
  have htrace : WordTrace (prefixWord ++ tailWord_442260) baseStart_442260 baseEnd_442260 := by
    simpa [prefixWord, tailWord_442260, baseEnd_442260] using wordTrace_append hprefix tailTrace_442260
  have hstable : (prefixWord ++ tailWord_442260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442260).length < 2 ^ (prefixWord ++ tailWord_442260).sum := by decide
  have hdescent : baseEnd_442260 < baseStart_442260 := by decide
  rcases family_descends (prefixWord ++ tailWord_442260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442350 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_442350 : Nat := 118140960795 + 442350 * 2 ^ 59
def prefixEnd_442350 : Nat := 4983230072969 + 3 ^ 40 * 442350 * 2
def baseEnd_442350 : Nat := 100950296673977572129189

theorem tailTrace_442350 : CollatzResearch.WordTrace tailWord_442350 prefixEnd_442350 100950296673977572129189 := by
  unfold tailWord_442350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2016728743431121526309563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10755886631632648140317669 2016728743431121526309563)
  ·
    refine ⟨3025093115146682289464345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2016728743431121526309563 3025093115146682289464345)
    ·
      refine ⟨2268819836360011717098259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3025093115146682289464345 2268819836360011717098259)
      ·
        refine ⟨3403229754540017575647389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2268819836360011717098259 3403229754540017575647389)
        ·
          refine ⟨1276211157952506590867771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3403229754540017575647389 1276211157952506590867771)
          ·
            refine ⟨1914316736928759886301657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276211157952506590867771 1914316736928759886301657)
            ·
              refine ⟨1435737552696569914726243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1914316736928759886301657 1435737552696569914726243)
              ·
                refine ⟨2153606329044854872089365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435737552696569914726243 2153606329044854872089365)
                ·
                  refine ⟨100950296673977572129189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2153606329044854872089365 100950296673977572129189)
                  ·
                    rfl

theorem cell21_442350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_442350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442350 prefixEnd_442350 := by exact prefixLift 442350
  have htrace : WordTrace (prefixWord ++ tailWord_442350) baseStart_442350 baseEnd_442350 := by
    simpa [prefixWord, tailWord_442350, baseEnd_442350] using wordTrace_append hprefix tailTrace_442350
  have hstable : (prefixWord ++ tailWord_442350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442350).length < 2 ^ (prefixWord ++ tailWord_442350).sum := by decide
  have hdescent : baseEnd_442350 < baseStart_442350 := by decide
  rcases family_descends (prefixWord ++ tailWord_442350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442353 : List Nat := [1, 2, 2, 2, 6, 1, 1, 1, 5]
def baseStart_442353 : Nat := 118140960795 + 442353 * 2 ^ 59
def prefixEnd_442353 : Nat := 4983230072969 + 3 ^ 40 * 442353 * 2
def baseEnd_442353 : Nat := 100950981314850233579183

theorem tailTrace_442353 : CollatzResearch.WordTrace tailWord_442353 prefixEnd_442353 100950981314850233579183 := by
  unfold tailWord_442353
  simp only [CollatzResearch.WordTrace]
  refine ⟨16133939366438103722835713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10755959577625402481890475 16133939366438103722835713)
  ·
    refine ⟨12100454524828577792126785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16133939366438103722835713 12100454524828577792126785)
    ·
      refine ⟨9075340893621433344095089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12100454524828577792126785 9075340893621433344095089)
      ·
        refine ⟨6806505670216075008071317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9075340893621433344095089 6806505670216075008071317)
        ·
          refine ⟨319054953291378516003343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6806505670216075008071317 319054953291378516003343)
          ·
            refine ⟨478582429937067774005015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319054953291378516003343 478582429937067774005015)
            ·
              refine ⟨717873644905601661007523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478582429937067774005015 717873644905601661007523)
              ·
                refine ⟨1076810467358402491511285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717873644905601661007523 1076810467358402491511285)
                ·
                  refine ⟨100950981314850233579183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1076810467358402491511285 100950981314850233579183)
                  ·
                    rfl

theorem cell21_442353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 5].length) (baseStart_442353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442353 prefixEnd_442353 := by exact prefixLift 442353
  have htrace : WordTrace (prefixWord ++ tailWord_442353) baseStart_442353 baseEnd_442353 := by
    simpa [prefixWord, tailWord_442353, baseEnd_442353] using wordTrace_append hprefix tailTrace_442353
  have hstable : (prefixWord ++ tailWord_442353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442353).length < 2 ^ (prefixWord ++ tailWord_442353).sum := by decide
  have hdescent : baseEnd_442353 < baseStart_442353 := by decide
  rcases family_descends (prefixWord ++ tailWord_442353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442364 : List Nat := [2, 2, 2, 1, 2, 2, 4, 6]
def baseStart_442364 : Nat := 118140960795 + 442364 * 2 ^ 59
def prefixEnd_442364 : Nat := 4983230072969 + 3 ^ 40 * 442364 * 2
def baseEnd_442364 : Nat := 33651163888238886298609

theorem tailTrace_442364 : CollatzResearch.WordTrace tailWord_442364 prefixEnd_442364 33651163888238886298609 := by
  unfold tailWord_442364
  simp only [CollatzResearch.WordTrace]
  refine ⟨8067170284699126300743073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10756227046265501734324097 8067170284699126300743073)
  ·
    refine ⟨6050377713524344725557305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8067170284699126300743073 6050377713524344725557305)
    ·
      refine ⟨4537783285143258544167979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6050377713524344725557305 4537783285143258544167979)
      ·
        refine ⟨6806674927714887816251969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4537783285143258544167979 6806674927714887816251969)
        ·
          refine ⟨5105006195786165862188977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6806674927714887816251969 5105006195786165862188977)
          ·
            refine ⟨3828754646839624396641733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5105006195786165862188977 3828754646839624396641733)
            ·
              refine ⟨717891496282429574370325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3828754646839624396641733 717891496282429574370325)
              ·
                refine ⟨33651163888238886298609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 717891496282429574370325 33651163888238886298609)
                ·
                  rfl

theorem cell21_442364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 6].length) (baseStart_442364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442364 prefixEnd_442364 := by exact prefixLift 442364
  have htrace : WordTrace (prefixWord ++ tailWord_442364) baseStart_442364 baseEnd_442364 := by
    simpa [prefixWord, tailWord_442364, baseEnd_442364] using wordTrace_append hprefix tailTrace_442364
  have hstable : (prefixWord ++ tailWord_442364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442364).length < 2 ^ (prefixWord ++ tailWord_442364).sum := by decide
  have hdescent : baseEnd_442364 < baseStart_442364 := by decide
  rcases family_descends (prefixWord ++ tailWord_442364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442471 : List Nat := [1, 1, 5, 1, 1, 2, 4, 1, 5]
def baseStart_442471 : Nat := 118140960795 + 442471 * 2 ^ 59
def prefixEnd_442471 : Nat := 4983230072969 + 3 ^ 40 * 442471 * 2
def baseEnd_442471 : Nat := 100977910522508250612275

theorem tailTrace_442471 : CollatzResearch.WordTrace tailWord_442471 prefixEnd_442471 100977910522508250612275 := by
  unfold tailWord_442471
  simp only [CollatzResearch.WordTrace]
  refine ⟨16138243180010609875631267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10758828786673739917087511 16138243180010609875631267)
  ·
    refine ⟨24207364770015914813446901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16138243180010609875631267 24207364770015914813446901)
    ·
      refine ⟨2269440447188992013760647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24207364770015914813446901 2269440447188992013760647)
      ·
        refine ⟨3404160670783488020640971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2269440447188992013760647 3404160670783488020640971)
        ·
          refine ⟨5106241006175232030961457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3404160670783488020640971 5106241006175232030961457)
          ·
            refine ⟨3829680754631424023221093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5106241006175232030961457 3829680754631424023221093)
            ·
              refine ⟨718065141493392004353955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3829680754631424023221093 718065141493392004353955)
              ·
                refine ⟨1077097712240088006530933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 718065141493392004353955 1077097712240088006530933)
                ·
                  refine ⟨100977910522508250612275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1077097712240088006530933 100977910522508250612275)
                  ·
                    rfl

theorem cell21_442471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 5].length) (baseStart_442471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442471 prefixEnd_442471 := by exact prefixLift 442471
  have htrace : WordTrace (prefixWord ++ tailWord_442471) baseStart_442471 baseEnd_442471 := by
    simpa [prefixWord, tailWord_442471, baseEnd_442471] using wordTrace_append hprefix tailTrace_442471
  have hstable : (prefixWord ++ tailWord_442471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442471).length < 2 ^ (prefixWord ++ tailWord_442471).sum := by decide
  have hdescent : baseEnd_442471 < baseStart_442471 := by decide
  rcases family_descends (prefixWord ++ tailWord_442471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442522 : List Nat := [3, 1, 1, 5, 2, 1, 3, 2, 3]
def baseStart_442522 : Nat := 118140960795 + 442522 * 2 ^ 59
def prefixEnd_442522 : Nat := 4983230072969 + 3 ^ 40 * 442522 * 2
def baseEnd_442522 : Nat := 100989549417343495262171

theorem tailTrace_442522 : CollatzResearch.WordTrace tailWord_442522 prefixEnd_442522 100989549417343495262171 := by
  unfold tailWord_442522
  simp only [CollatzResearch.WordTrace]
  refine ⟨4035025825706461396434455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10760068868550563723825213 4035025825706461396434455)
  ·
    refine ⟨6052538738559692094651683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4035025825706461396434455 6052538738559692094651683)
    ·
      refine ⟨9078808107839538141977525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6052538738559692094651683 9078808107839538141977525)
      ·
        refine ⟨851138260109956700810393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9078808107839538141977525 851138260109956700810393)
        ·
          refine ⟨638353695082467525607795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 851138260109956700810393 638353695082467525607795)
          ·
            refine ⟨957530542623701288411693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638353695082467525607795 957530542623701288411693)
            ·
              refine ⟨359073953483887983154385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 957530542623701288411693 359073953483887983154385)
              ·
                refine ⟨269305465112915987365789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359073953483887983154385 269305465112915987365789)
                ·
                  refine ⟨100989549417343495262171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269305465112915987365789 100989549417343495262171)
                  ·
                    rfl

theorem cell21_442522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_442522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442522 prefixEnd_442522 := by exact prefixLift 442522
  have htrace : WordTrace (prefixWord ++ tailWord_442522) baseStart_442522 baseEnd_442522 := by
    simpa [prefixWord, tailWord_442522, baseEnd_442522] using wordTrace_append hprefix tailTrace_442522
  have hstable : (prefixWord ++ tailWord_442522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442522).length < 2 ^ (prefixWord ++ tailWord_442522).sum := by decide
  have hdescent : baseEnd_442522 < baseStart_442522 := by decide
  rcases family_descends (prefixWord ++ tailWord_442522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442578 : List Nat := [3, 2, 2, 2, 1, 2, 1, 4, 4]
def baseStart_442578 : Nat := 118140960795 + 442578 * 2 ^ 59
def prefixEnd_442578 : Nat := 4983230072969 + 3 ^ 40 * 442578 * 2
def baseEnd_442578 : Nat := 101002329380299842328723

theorem tailTrace_442578 : CollatzResearch.WordTrace tailWord_442578 prefixEnd_442578 101002329380299842328723 := by
  unfold tailWord_442578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4035536447655741787444097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10761430527081978099850925 4035536447655741787444097)
  ·
    refine ⟨3026652335741806340583073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4035536447655741787444097 3026652335741806340583073)
    ·
      refine ⟨2269989251806354755437305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3026652335741806340583073 2269989251806354755437305)
      ·
        refine ⟨1702491938854766066577979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2269989251806354755437305 1702491938854766066577979)
        ·
          refine ⟨2553737908282149099866969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1702491938854766066577979 2553737908282149099866969)
          ·
            refine ⟨1915303431211611824900227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2553737908282149099866969 1915303431211611824900227)
            ·
              refine ⟨2872955146817417737350341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1915303431211611824900227 2872955146817417737350341)
              ·
                refine ⟨538679090028265825753189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2872955146817417737350341 538679090028265825753189)
                ·
                  refine ⟨101002329380299842328723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 538679090028265825753189 101002329380299842328723)
                  ·
                    rfl

theorem cell21_442578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_442578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442578 prefixEnd_442578 := by exact prefixLift 442578
  have htrace : WordTrace (prefixWord ++ tailWord_442578) baseStart_442578 baseEnd_442578 := by
    simpa [prefixWord, tailWord_442578, baseEnd_442578] using wordTrace_append hprefix tailTrace_442578
  have hstable : (prefixWord ++ tailWord_442578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442578).length < 2 ^ (prefixWord ++ tailWord_442578).sum := by decide
  have hdescent : baseEnd_442578 < baseStart_442578 := by decide
  rcases family_descends (prefixWord ++ tailWord_442578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442581 : List Nat := [1, 3, 2, 4, 2, 1, 1, 4, 3]
def baseStart_442581 : Nat := 118140960795 + 442581 * 2 ^ 59
def prefixEnd_442581 : Nat := 4983230072969 + 3 ^ 40 * 442581 * 2
def baseEnd_442581 : Nat := 101003014021172503778717

theorem tailTrace_442581 : CollatzResearch.WordTrace tailWord_442581 prefixEnd_442581 101003014021172503778717 := by
  unfold tailWord_442581
  simp only [CollatzResearch.WordTrace]
  refine ⟨16142255209612098662135597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10761503473074732441423731 16142255209612098662135597)
  ·
    refine ⟨6053345703604536998300849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16142255209612098662135597 6053345703604536998300849)
    ·
      refine ⟨4540009277703402748725637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6053345703604536998300849 4540009277703402748725637)
      ·
        refine ⟨851251739569388015386057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4540009277703402748725637 851251739569388015386057)
        ·
          refine ⟨638438804677041011539543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 851251739569388015386057 638438804677041011539543)
          ·
            refine ⟨957658207015561517309315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638438804677041011539543 957658207015561517309315)
            ·
              refine ⟨1436487310523342275963973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957658207015561517309315 1436487310523342275963973)
              ·
                refine ⟨269341370723126676743245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1436487310523342275963973 269341370723126676743245)
                ·
                  refine ⟨101003014021172503778717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269341370723126676743245 101003014021172503778717)
                  ·
                    rfl

theorem cell21_442581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_442581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442581 prefixEnd_442581 := by exact prefixLift 442581
  have htrace : WordTrace (prefixWord ++ tailWord_442581) baseStart_442581 baseEnd_442581 := by
    simpa [prefixWord, tailWord_442581, baseEnd_442581] using wordTrace_append hprefix tailTrace_442581
  have hstable : (prefixWord ++ tailWord_442581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442581).length < 2 ^ (prefixWord ++ tailWord_442581).sum := by decide
  have hdescent : baseEnd_442581 < baseStart_442581 := by decide
  rcases family_descends (prefixWord ++ tailWord_442581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442668 : List Nat := [2, 2, 1, 1, 1, 3, 6, 5]
def baseStart_442668 : Nat := 118140960795 + 442668 * 2 ^ 59
def prefixEnd_442668 : Nat := 4983230072969 + 3 ^ 40 * 442668 * 2
def baseEnd_442668 : Nat := 33674289535493228609513

theorem tailTrace_442668 : CollatzResearch.WordTrace tailWord_442668 prefixEnd_442668 33674289535493228609513 := by
  unfold tailWord_442668
  simp only [CollatzResearch.WordTrace]
  refine ⟨8072714180148456260276329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10763618906864608347035105 8072714180148456260276329)
  ·
    refine ⟨6054535635111342195207247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8072714180148456260276329 6054535635111342195207247)
    ·
      refine ⟨9081803452667013292810871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6054535635111342195207247 9081803452667013292810871)
      ·
        refine ⟨13622705179000519939216307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9081803452667013292810871 13622705179000519939216307)
        ·
          refine ⟨20434057768500779908824461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13622705179000519939216307 20434057768500779908824461)
          ·
            refine ⟨7662771663187792465809173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20434057768500779908824461 7662771663187792465809173)
            ·
              refine ⟨359192421711927771834805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7662771663187792465809173 359192421711927771834805)
              ·
                refine ⟨33674289535493228609513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 359192421711927771834805 33674289535493228609513)
                ·
                  rfl

theorem cell21_442668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 5].length) (baseStart_442668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442668 prefixEnd_442668 := by exact prefixLift 442668
  have htrace : WordTrace (prefixWord ++ tailWord_442668) baseStart_442668 baseEnd_442668 := by
    simpa [prefixWord, tailWord_442668, baseEnd_442668] using wordTrace_append hprefix tailTrace_442668
  have hstable : (prefixWord ++ tailWord_442668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442668).length < 2 ^ (prefixWord ++ tailWord_442668).sum := by decide
  have hdescent : baseEnd_442668 < baseStart_442668 := by decide
  rcases family_descends (prefixWord ++ tailWord_442668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442674 : List Nat := [3, 2, 1, 1, 6, 1, 1, 3, 3]
def baseStart_442674 : Nat := 118140960795 + 442674 * 2 ^ 59
def prefixEnd_442674 : Nat := 4983230072969 + 3 ^ 40 * 442674 * 2
def baseEnd_442674 : Nat := 101024237888225008728527

theorem tailTrace_442674 : CollatzResearch.WordTrace tailWord_442674 prefixEnd_442674 101024237888225008728527 := by
  unfold tailWord_442674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4036411799568793886317769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10763764798850117030180717 4036411799568793886317769)
  ·
    refine ⟨3027308849676595414738327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4036411799568793886317769 3027308849676595414738327)
    ·
      refine ⟨4540963274514893122107491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3027308849676595414738327 4540963274514893122107491)
      ·
        refine ⟨6811444911772339683161237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4540963274514893122107491 6811444911772339683161237)
        ·
          refine ⟨319286480239328422648183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6811444911772339683161237 319286480239328422648183)
          ·
            refine ⟨478929720358992633972275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319286480239328422648183 478929720358992633972275)
            ·
              refine ⟨718394580538488950958413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478929720358992633972275 718394580538488950958413)
              ·
                refine ⟨269397967701933356609405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 718394580538488950958413 269397967701933356609405)
                ·
                  refine ⟨101024237888225008728527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269397967701933356609405 101024237888225008728527)
                  ·
                    rfl

theorem cell21_442674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_442674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442674 prefixEnd_442674 := by exact prefixLift 442674
  have htrace : WordTrace (prefixWord ++ tailWord_442674) baseStart_442674 baseEnd_442674 := by
    simpa [prefixWord, tailWord_442674, baseEnd_442674] using wordTrace_append hprefix tailTrace_442674
  have hstable : (prefixWord ++ tailWord_442674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442674).length < 2 ^ (prefixWord ++ tailWord_442674).sum := by decide
  have hdescent : baseEnd_442674 < baseStart_442674 := by decide
  rcases family_descends (prefixWord ++ tailWord_442674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442837 : List Nat := [1, 3, 2, 3, 1, 4, 2, 5]
def baseStart_442837 : Nat := 118140960795 + 442837 * 2 ^ 59
def prefixEnd_442837 : Nat := 4983230072969 + 3 ^ 40 * 442837 * 2
def baseEnd_442837 : Nat := 33687145569657649170509

theorem tailTrace_442837 : CollatzResearch.WordTrace tailWord_442837 prefixEnd_442837 33687145569657649170509 := by
  unfold tailWord_442837
  simp only [CollatzResearch.WordTrace]
  refine ⟨16151592296684654383454765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10767728197789769588969843 16151592296684654383454765)
  ·
    refine ⟨6056847111256745393795537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16151592296684654383454765 6056847111256745393795537)
    ·
      refine ⟨4542635333442559045346653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6056847111256745393795537 4542635333442559045346653)
      ·
        refine ⟨1703488250040959642004995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4542635333442559045346653 1703488250040959642004995)
        ·
          refine ⟨2555232375061439463007493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1703488250040959642004995 2555232375061439463007493)
          ·
            refine ⟨479106070324019899313905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2555232375061439463007493 479106070324019899313905)
            ·
              refine ⟨359329552743014924485429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479106070324019899313905 359329552743014924485429)
              ·
                refine ⟨33687145569657649170509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 359329552743014924485429 33687145569657649170509)
                ·
                  rfl

theorem cell21_442837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 5].length) (baseStart_442837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442837 prefixEnd_442837 := by exact prefixLift 442837
  have htrace : WordTrace (prefixWord ++ tailWord_442837) baseStart_442837 baseEnd_442837 := by
    simpa [prefixWord, tailWord_442837, baseEnd_442837] using wordTrace_append hprefix tailTrace_442837
  have hstable : (prefixWord ++ tailWord_442837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442837).length < 2 ^ (prefixWord ++ tailWord_442837).sum := by decide
  have hdescent : baseEnd_442837 < baseStart_442837 := by decide
  rcases family_descends (prefixWord ++ tailWord_442837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442848 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 8]
def baseStart_442848 : Nat := 118140960795 + 442848 * 2 ^ 59
def prefixEnd_442848 : Nat := 4983230072969 + 3 ^ 40 * 442848 * 2
def baseEnd_442848 : Nat := 101063947058839372828171

theorem tailTrace_442848 : CollatzResearch.WordTrace tailWord_442848 prefixEnd_442848 101063947058839372828171 := by
  unfold tailWord_442848
  simp only [CollatzResearch.WordTrace]
  refine ⟨8075996749822401631052599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10767995666429868841403465 8075996749822401631052599)
  ·
    refine ⟨12113995124733602446578899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8075996749822401631052599 12113995124733602446578899)
    ·
      refine ⟨18170992687100403669868349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12113995124733602446578899 18170992687100403669868349)
      ·
        refine ⟨6814122257662651376200631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18170992687100403669868349 6814122257662651376200631)
        ·
          refine ⟨10221183386493977064300947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6814122257662651376200631 10221183386493977064300947)
          ·
            refine ⟨15331775079740965596451421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10221183386493977064300947 15331775079740965596451421)
            ·
              refine ⟨5749415654902862098669283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15331775079740965596451421 5749415654902862098669283)
              ·
                refine ⟨8624123482354293148003925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5749415654902862098669283 8624123482354293148003925)
                ·
                  refine ⟨101063947058839372828171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8624123482354293148003925 101063947058839372828171)
                  ·
                    rfl

theorem cell21_442848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_442848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442848 prefixEnd_442848 := by exact prefixLift 442848
  have htrace : WordTrace (prefixWord ++ tailWord_442848) baseStart_442848 baseEnd_442848 := by
    simpa [prefixWord, tailWord_442848, baseEnd_442848] using wordTrace_append hprefix tailTrace_442848
  have hstable : (prefixWord ++ tailWord_442848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442848).length < 2 ^ (prefixWord ++ tailWord_442848).sum := by decide
  have hdescent : baseEnd_442848 < baseStart_442848 := by decide
  rcases family_descends (prefixWord ++ tailWord_442848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442865 : List Nat := [1, 2, 2, 2, 3, 1, 2, 4, 4]
def baseStart_442865 : Nat := 118140960795 + 442865 * 2 ^ 59
def prefixEnd_442865 : Nat := 4983230072969 + 3 ^ 40 * 442865 * 2
def baseEnd_442865 : Nat := 101067826690451121044803

theorem tailTrace_442865 : CollatzResearch.WordTrace tailWord_442865 prefixEnd_442865 101067826690451121044803 := by
  unfold tailWord_442865
  simp only [CollatzResearch.WordTrace]
  refine ⟨16152613540583215165474049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10768409027055476776982699 16152613540583215165474049)
  ·
    refine ⟨12114460155437411374105537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16152613540583215165474049 12114460155437411374105537)
    ·
      refine ⟨9085845116578058530579153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12114460155437411374105537 9085845116578058530579153)
      ·
        refine ⟨6814383837433543897934365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9085845116578058530579153 6814383837433543897934365)
        ·
          refine ⟨2555393939037578961725387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6814383837433543897934365 2555393939037578961725387)
          ·
            refine ⟨3833090908556368442588081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555393939037578961725387 3833090908556368442588081)
            ·
              refine ⟨2874818181417276331941061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3833090908556368442588081 2874818181417276331941061)
              ·
                refine ⟨539028409015739312238949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2874818181417276331941061 539028409015739312238949)
                ·
                  refine ⟨101067826690451121044803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 539028409015739312238949 101067826690451121044803)
                  ·
                    rfl

theorem cell21_442865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_442865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442865 prefixEnd_442865 := by exact prefixLift 442865
  have htrace : WordTrace (prefixWord ++ tailWord_442865) baseStart_442865 baseEnd_442865 := by
    simpa [prefixWord, tailWord_442865, baseEnd_442865] using wordTrace_append hprefix tailTrace_442865
  have hstable : (prefixWord ++ tailWord_442865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442865).length < 2 ^ (prefixWord ++ tailWord_442865).sum := by decide
  have hdescent : baseEnd_442865 < baseStart_442865 := by decide
  rcases family_descends (prefixWord ++ tailWord_442865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442879 : List Nat := [1, 1, 2, 2, 1, 2, 6, 6]
def baseStart_442879 : Nat := 118140960795 + 442879 * 2 ^ 59
def prefixEnd_442879 : Nat := 4983230072969 + 3 ^ 40 * 442879 * 2
def baseEnd_442879 : Nat := 33690340560396735937147

theorem tailTrace_442879 : CollatzResearch.WordTrace tailWord_442879 prefixEnd_442879 33690340560396735937147 := by
  unfold tailWord_442879
  simp only [CollatzResearch.WordTrace]
  refine ⟨16153124162532495556483691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10768749441688330370989127 16153124162532495556483691)
  ·
    refine ⟨24229686243798743334725537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16153124162532495556483691 24229686243798743334725537)
    ·
      refine ⟨18172264682849057501044153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24229686243798743334725537 18172264682849057501044153)
      ·
        refine ⟨13629198512136793125783115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18172264682849057501044153 13629198512136793125783115)
        ·
          refine ⟨20443797768205189688674673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13629198512136793125783115 20443797768205189688674673)
          ·
            refine ⟨15332848326153892266506005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20443797768205189688674673 15332848326153892266506005)
            ·
              refine ⟨718727265288463699992469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15332848326153892266506005 718727265288463699992469)
              ·
                refine ⟨33690340560396735937147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 718727265288463699992469 33690340560396735937147)
                ·
                  rfl

theorem cell21_442879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 6].length) (baseStart_442879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442879 prefixEnd_442879 := by exact prefixLift 442879
  have htrace : WordTrace (prefixWord ++ tailWord_442879) baseStart_442879 baseEnd_442879 := by
    simpa [prefixWord, tailWord_442879, baseEnd_442879] using wordTrace_append hprefix tailTrace_442879
  have hstable : (prefixWord ++ tailWord_442879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442879).length < 2 ^ (prefixWord ++ tailWord_442879).sum := by decide
  have hdescent : baseEnd_442879 < baseStart_442879 := by decide
  rcases family_descends (prefixWord ++ tailWord_442879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442919 : List Nat := [1, 1, 7, 2, 1, 2, 2, 2, 3]
def baseStart_442919 : Nat := 118140960795 + 442919 * 2 ^ 59
def prefixEnd_442919 : Nat := 4983230072969 + 3 ^ 40 * 442919 * 2
def baseEnd_442919 : Nat := 101080150226159027144693

theorem tailTrace_442919 : CollatzResearch.WordTrace tailWord_442919 prefixEnd_442919 101080150226159027144693 := by
  unfold tailWord_442919
  simp only [CollatzResearch.WordTrace]
  refine ⟨16154583082387582387939811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10769722054925054925293207 16154583082387582387939811)
  ·
    refine ⟨24231874623581373581909717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16154583082387582387939811 24231874623581373581909717)
    ·
      refine ⟨567934561490188443326009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 24231874623581373581909717 567934561490188443326009)
      ·
        refine ⟨425950921117641332494507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567934561490188443326009 425950921117641332494507)
        ·
          refine ⟨638926381676461998741761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425950921117641332494507 638926381676461998741761)
          ·
            refine ⟨479194786257346499056321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638926381676461998741761 479194786257346499056321)
            ·
              refine ⟨359396089693009874292241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479194786257346499056321 359396089693009874292241)
              ·
                refine ⟨269547067269757405719181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359396089693009874292241 269547067269757405719181)
                ·
                  refine ⟨101080150226159027144693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269547067269757405719181 101080150226159027144693)
                  ·
                    rfl

theorem cell21_442919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 3].length) (baseStart_442919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442919 prefixEnd_442919 := by exact prefixLift 442919
  have htrace : WordTrace (prefixWord ++ tailWord_442919) baseStart_442919 baseEnd_442919 := by
    simpa [prefixWord, tailWord_442919, baseEnd_442919] using wordTrace_append hprefix tailTrace_442919
  have hstable : (prefixWord ++ tailWord_442919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442919).length < 2 ^ (prefixWord ++ tailWord_442919).sum := by decide
  have hdescent : baseEnd_442919 < baseStart_442919 := by decide
  rcases family_descends (prefixWord ++ tailWord_442919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442924 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 6]
def baseStart_442924 : Nat := 118140960795 + 442924 * 2 ^ 59
def prefixEnd_442924 : Nat := 4983230072969 + 3 ^ 40 * 442924 * 2
def baseEnd_442924 : Nat := 101081291294280129561349

theorem tailTrace_442924 : CollatzResearch.WordTrace tailWord_442924 prefixEnd_442924 101081291294280129561349 := by
  unfold tailWord_442924
  simp only [CollatzResearch.WordTrace]
  refine ⟨8077382723684734120935913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10769843631579645494581217 8077382723684734120935913)
  ·
    refine ⟨6058037042763550590701935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8077382723684734120935913 6058037042763550590701935)
    ·
      refine ⟨9087055564145325886052903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6058037042763550590701935 9087055564145325886052903)
      ·
        refine ⟨13630583346217988829079355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9087055564145325886052903 13630583346217988829079355)
        ·
          refine ⟨20445875019326983243619033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13630583346217988829079355 20445875019326983243619033)
          ·
            refine ⟨15334406264495237432714275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20445875019326983243619033 15334406264495237432714275)
            ·
              refine ⟨23001609396742856149071413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15334406264495237432714275 23001609396742856149071413)
              ·
                refine ⟨2156400880944642763975445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23001609396742856149071413 2156400880944642763975445)
                ·
                  refine ⟨101081291294280129561349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2156400880944642763975445 101081291294280129561349)
                  ·
                    rfl

theorem cell21_442924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_442924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442924 prefixEnd_442924 := by exact prefixLift 442924
  have htrace : WordTrace (prefixWord ++ tailWord_442924) baseStart_442924 baseEnd_442924 := by
    simpa [prefixWord, tailWord_442924, baseEnd_442924] using wordTrace_append hprefix tailTrace_442924
  have hstable : (prefixWord ++ tailWord_442924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442924).length < 2 ^ (prefixWord ++ tailWord_442924).sum := by decide
  have hdescent : baseEnd_442924 < baseStart_442924 := by decide
  rcases family_descends (prefixWord ++ tailWord_442924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442972 : List Nat := [2, 2, 4, 1, 3, 1, 8]
def baseStart_442972 : Nat := 118140960795 + 442972 * 2 ^ 59
def prefixEnd_442972 : Nat := 4983230072969 + 3 ^ 40 * 442972 * 2
def baseEnd_442972 : Nat := 11232471727582523640139

theorem tailTrace_442972 : CollatzResearch.WordTrace tailWord_442972 prefixEnd_442972 11232471727582523640139 := by
  unfold tailWord_442972
  simp only [CollatzResearch.WordTrace]
  refine ⟨8078258075597786219809585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10771010767463714959746113 8078258075597786219809585)
  ·
    refine ⟨6058693556698339664857189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8078258075597786219809585 6058693556698339664857189)
    ·
      refine ⟨1136005041880938687160723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6058693556698339664857189 1136005041880938687160723)
      ·
        refine ⟨1704007562821408030741085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1136005041880938687160723 1704007562821408030741085)
        ·
          refine ⟨639002836058028011527907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1704007562821408030741085 639002836058028011527907)
          ·
            refine ⟨958504254087042017291861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639002836058028011527907 958504254087042017291861)
            ·
              refine ⟨11232471727582523640139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 958504254087042017291861 11232471727582523640139)
              ·
                rfl

theorem cell21_442972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 8].length) (baseStart_442972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_442972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_442972 prefixEnd_442972 := by exact prefixLift 442972
  have htrace : WordTrace (prefixWord ++ tailWord_442972) baseStart_442972 baseEnd_442972 := by
    simpa [prefixWord, tailWord_442972, baseEnd_442972] using wordTrace_append hprefix tailTrace_442972
  have hstable : (prefixWord ++ tailWord_442972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442972).length < 2 ^ (prefixWord ++ tailWord_442972).sum := by decide
  have hdescent : baseEnd_442972 < baseStart_442972 := by decide
  rcases family_descends (prefixWord ++ tailWord_442972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443096 : List Nat := [2, 1, 2, 2, 3, 2, 4, 2, 3]
def baseStart_443096 : Nat := 118140960795 + 443096 * 2 ^ 59
def prefixEnd_443096 : Nat := 4983230072969 + 3 ^ 40 * 443096 * 2
def baseEnd_443096 : Nat := 101120544037646052694331

theorem tailTrace_443096 : CollatzResearch.WordTrace tailWord_443096 prefixEnd_443096 101120544037646052694331 := by
  unfold tailWord_443096
  simp only [CollatzResearch.WordTrace]
  refine ⟨8080519401373170808566571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10774025868497561078088761 8080519401373170808566571)
  ·
    refine ⟨12120779102059756212849857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8080519401373170808566571 12120779102059756212849857)
    ·
      refine ⟨9090584326544817159637393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12120779102059756212849857 9090584326544817159637393)
      ·
        refine ⟨6817938244908612869728045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9090584326544817159637393 6817938244908612869728045)
        ·
          refine ⟨2556726841840729826148017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6817938244908612869728045 2556726841840729826148017)
          ·
            refine ⟨1917545131380547369611013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2556726841840729826148017 1917545131380547369611013)
            ·
              refine ⟨359539712133852631802065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1917545131380547369611013 359539712133852631802065)
              ·
                refine ⟨269654784100389473851549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359539712133852631802065 269654784100389473851549)
                ·
                  refine ⟨101120544037646052694331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269654784100389473851549 101120544037646052694331)
                  ·
                    rfl

theorem cell21_443096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 3].length) (baseStart_443096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_443096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_443096 prefixEnd_443096 := by exact prefixLift 443096
  have htrace : WordTrace (prefixWord ++ tailWord_443096) baseStart_443096 baseEnd_443096 := by
    simpa [prefixWord, tailWord_443096, baseEnd_443096] using wordTrace_append hprefix tailTrace_443096
  have hstable : (prefixWord ++ tailWord_443096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443096).length < 2 ^ (prefixWord ++ tailWord_443096).sum := by decide
  have hdescent : baseEnd_443096 < baseStart_443096 := by decide
  rcases family_descends (prefixWord ++ tailWord_443096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443206 : List Nat := [6, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_443206 : Nat := 118140960795 + 443206 * 2 ^ 59
def prefixEnd_443206 : Nat := 4983230072969 + 3 ^ 40 * 443206 * 2
def baseEnd_443206 : Nat := 101145647536310305860773

theorem tailTrace_443206 : CollatzResearch.WordTrace tailWord_443206 prefixEnd_443206 101145647536310305860773 := by
  unfold tailWord_443206
  simp only [CollatzResearch.WordTrace]
  refine ⟨505157838510869700113671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10776700554898553602424981 505157838510869700113671)
  ·
    refine ⟨757736757766304550170507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 505157838510869700113671 757736757766304550170507)
    ·
      refine ⟨1136605136649456825255761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 757736757766304550170507 1136605136649456825255761)
      ·
        refine ⟨852453852487092618941821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1136605136649456825255761 852453852487092618941821)
        ·
          refine ⟨319670194682659732103183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 852453852487092618941821 319670194682659732103183)
          ·
            refine ⟨479505292023989598154775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319670194682659732103183 479505292023989598154775)
            ·
              refine ⟨719257938035984397232163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479505292023989598154775 719257938035984397232163)
              ·
                refine ⟨1078886907053976595848245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719257938035984397232163 1078886907053976595848245)
                ·
                  refine ⟨101145647536310305860773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1078886907053976595848245 101145647536310305860773)
                  ·
                    rfl

theorem cell21_443206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_443206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_443206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_443206 prefixEnd_443206 := by exact prefixLift 443206
  have htrace : WordTrace (prefixWord ++ tailWord_443206) baseStart_443206 baseEnd_443206 := by
    simpa [prefixWord, tailWord_443206, baseEnd_443206] using wordTrace_append hprefix tailTrace_443206
  have hstable : (prefixWord ++ tailWord_443206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443206).length < 2 ^ (prefixWord ++ tailWord_443206).sum := by decide
  have hdescent : baseEnd_443206 < baseStart_443206 := by decide
  rcases family_descends (prefixWord ++ tailWord_443206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443220 : List Nat := [2, 4, 1, 1, 5, 1, 2, 1, 4]
def baseStart_443220 : Nat := 118140960795 + 443220 * 2 ^ 59
def prefixEnd_443220 : Nat := 4983230072969 + 3 ^ 40 * 443220 * 2
def baseEnd_443220 : Nat := 101148842527049392627411

theorem tailTrace_443220 : CollatzResearch.WordTrace tailWord_443220 prefixEnd_443220 101148842527049392627411 := by
  unfold tailWord_443220
  simp only [CollatzResearch.WordTrace]
  refine ⟨8082780727148555397323557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10777040969531407196431409 8082780727148555397323557)
  ·
    refine ⟨1515521386340354136998167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8082780727148555397323557 1515521386340354136998167)
    ·
      refine ⟨2273282079510531205497251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1515521386340354136998167 2273282079510531205497251)
      ·
        refine ⟨3409923119265796808245877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2273282079510531205497251 3409923119265796808245877)
        ·
          refine ⟨319680292431168450773051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3409923119265796808245877 319680292431168450773051)
          ·
            refine ⟨479520438646752676159577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319680292431168450773051 479520438646752676159577)
            ·
              refine ⟨359640328985064507119683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479520438646752676159577 359640328985064507119683)
              ·
                refine ⟨539460493477596760679525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359640328985064507119683 539460493477596760679525)
                ·
                  refine ⟨101148842527049392627411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 539460493477596760679525 101148842527049392627411)
                  ·
                    rfl

theorem cell21_443220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_443220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_443220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_443220 prefixEnd_443220 := by exact prefixLift 443220
  have htrace : WordTrace (prefixWord ++ tailWord_443220) baseStart_443220 baseEnd_443220 := by
    simpa [prefixWord, tailWord_443220, baseEnd_443220] using wordTrace_append hprefix tailTrace_443220
  have hstable : (prefixWord ++ tailWord_443220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443220).length < 2 ^ (prefixWord ++ tailWord_443220).sum := by decide
  have hdescent : baseEnd_443220 < baseStart_443220 := by decide
  rcases family_descends (prefixWord ++ tailWord_443220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443321 : List Nat := [1, 2, 1, 4, 2, 2, 3, 2, 4]
def baseStart_443321 : Nat := 118140960795 + 443321 * 2 ^ 59
def prefixEnd_443321 : Nat := 4983230072969 + 3 ^ 40 * 443321 * 2
def baseEnd_443321 : Nat := 101171892103095661443871

theorem tailTrace_443321 : CollatzResearch.WordTrace tailWord_443321 prefixEnd_443321 101171892103095661443871 := by
  unfold tailWord_443321
  simp only [CollatzResearch.WordTrace]
  refine ⟨16169245226931205044073817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10779496817954136696049211 16169245226931205044073817)
  ·
    refine ⟨12126933920198403783055363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16169245226931205044073817 12126933920198403783055363)
    ·
      refine ⟨18190400880297605674583045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12126933920198403783055363 18190400880297605674583045)
      ·
        refine ⟨3410700165055801063984321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18190400880297605674583045 3410700165055801063984321)
        ·
          refine ⟨2558025123791850797988241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3410700165055801063984321 2558025123791850797988241)
          ·
            refine ⟨1918518842843888098491181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2558025123791850797988241 1918518842843888098491181)
            ·
              refine ⟨719444566066458036934193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1918518842843888098491181 719444566066458036934193)
              ·
                refine ⟨539583424549843527700645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 719444566066458036934193 539583424549843527700645)
                ·
                  refine ⟨101171892103095661443871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 539583424549843527700645 101171892103095661443871)
                  ·
                    rfl

theorem cell21_443321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_443321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_443321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_443321 prefixEnd_443321 := by exact prefixLift 443321
  have htrace : WordTrace (prefixWord ++ tailWord_443321) baseStart_443321 baseEnd_443321 := by
    simpa [prefixWord, tailWord_443321, baseEnd_443321] using wordTrace_append hprefix tailTrace_443321
  have hstable : (prefixWord ++ tailWord_443321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443321).length < 2 ^ (prefixWord ++ tailWord_443321).sum := by decide
  have hdescent : baseEnd_443321 < baseStart_443321 := by decide
  rcases family_descends (prefixWord ++ tailWord_443321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443352 : List Nat := [2, 1, 2, 2, 2, 5, 2, 5]
def baseStart_443352 : Nat := 118140960795 + 443352 * 2 ^ 59
def prefixEnd_443352 : Nat := 4983230072969 + 3 ^ 40 * 443352 * 2
def baseEnd_443352 : Nat := 33726322241815498809047

theorem tailTrace_443352 : CollatzResearch.WordTrace tailWord_443352 prefixEnd_443352 33726322241815498809047 := by
  unfold tailWord_443352
  simp only [CollatzResearch.WordTrace]
  refine ⟨8085187944909448669226155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10780250593212598225634873 8085187944909448669226155)
  ·
    refine ⟨12127781917364173003839233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8085187944909448669226155 12127781917364173003839233)
    ·
      refine ⟨9095836438023129752879425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12127781917364173003839233 9095836438023129752879425)
      ·
        refine ⟨6821877328517347314659569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9095836438023129752879425 6821877328517347314659569)
        ·
          refine ⟨5116407996388010485994677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6821877328517347314659569 5116407996388010485994677)
          ·
            refine ⟨479663249661375983062001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5116407996388010485994677 479663249661375983062001)
            ·
              refine ⟨359747437246031987296501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479663249661375983062001 359747437246031987296501)
              ·
                refine ⟨33726322241815498809047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 359747437246031987296501 33726322241815498809047)
                ·
                  rfl

theorem cell21_443352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 5].length) (baseStart_443352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_443352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_443352 prefixEnd_443352 := by exact prefixLift 443352
  have htrace : WordTrace (prefixWord ++ tailWord_443352) baseStart_443352 baseEnd_443352 := by
    simpa [prefixWord, tailWord_443352, baseEnd_443352] using wordTrace_append hprefix tailTrace_443352
  have hstable : (prefixWord ++ tailWord_443352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443352).length < 2 ^ (prefixWord ++ tailWord_443352).sum := by decide
  have hdescent : baseEnd_443352 < baseStart_443352 := by decide
  rcases family_descends (prefixWord ++ tailWord_443352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443434 : List Nat := [3, 1, 4, 1, 4, 1, 2, 2, 3]
def baseStart_443434 : Nat := 118140960795 + 443434 * 2 ^ 59
def prefixEnd_443434 : Nat := 4983230072969 + 3 ^ 40 * 443434 * 2
def baseEnd_443434 : Nat := 101197680242632576060307

theorem tailTrace_443434 : CollatzResearch.WordTrace tailWord_443434 prefixEnd_443434 101197680242632576060307 := by
  unfold tailWord_443434
  simp only [CollatzResearch.WordTrace]
  refine ⟨4043341668880456335734339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10782244450347883561958237 4043341668880456335734339)
  ·
    refine ⟨6065012503320684503601509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4043341668880456335734339 6065012503320684503601509)
    ·
      refine ⟨1137189844372628344425283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6065012503320684503601509 1137189844372628344425283)
      ·
        refine ⟨1705784766558942516637925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1137189844372628344425283 1705784766558942516637925)
        ·
          refine ⟨319834643729801721869611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1705784766558942516637925 319834643729801721869611)
          ·
            refine ⟨479751965594702582804417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319834643729801721869611 479751965594702582804417)
            ·
              refine ⟨359813974196026937103313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479751965594702582804417 359813974196026937103313)
              ·
                refine ⟨269860480647020202827485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359813974196026937103313 269860480647020202827485)
                ·
                  refine ⟨101197680242632576060307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269860480647020202827485 101197680242632576060307)
                  ·
                    rfl

theorem cell21_443434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_443434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_443434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_443434 prefixEnd_443434 := by exact prefixLift 443434
  have htrace : WordTrace (prefixWord ++ tailWord_443434) baseStart_443434 baseEnd_443434 := by
    simpa [prefixWord, tailWord_443434, baseEnd_443434] using wordTrace_append hprefix tailTrace_443434
  have hstable : (prefixWord ++ tailWord_443434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443434).length < 2 ^ (prefixWord ++ tailWord_443434).sum := by decide
  have hdescent : baseEnd_443434 < baseStart_443434 := by decide
  rcases family_descends (prefixWord ++ tailWord_443434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443439 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 10]
def baseStart_443439 : Nat := 118140960795 + 443439 * 2 ^ 59
def prefixEnd_443439 : Nat := 4983230072969 + 3 ^ 40 * 443439 * 2
def baseEnd_443439 : Nat := 101198821310753678476963

theorem tailTrace_443439 : CollatzResearch.WordTrace tailWord_443439 prefixEnd_443439 101198821310753678476963 := by
  unfold tailWord_443439
  simp only [CollatzResearch.WordTrace]
  refine ⟨16173549040503711196869371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10782366027002474131246247 16173549040503711196869371)
  ·
    refine ⟨24260323560755566795304057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16173549040503711196869371 24260323560755566795304057)
    ·
      refine ⟨18195242670566675096478043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24260323560755566795304057 18195242670566675096478043)
      ·
        refine ⟨27292864005850012644717065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18195242670566675096478043 27292864005850012644717065)
        ·
          refine ⟨20469648004387509483537799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27292864005850012644717065 20469648004387509483537799)
          ·
            refine ⟨30704472006581264225306699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20469648004387509483537799 30704472006581264225306699)
            ·
              refine ⟨46056708009871896337960049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30704472006581264225306699 46056708009871896337960049)
              ·
                refine ⟨34542531007403922253470037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46056708009871896337960049 34542531007403922253470037)
                ·
                  refine ⟨101198821310753678476963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 34542531007403922253470037 101198821310753678476963)
                  ·
                    rfl

theorem cell21_443439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 10].length) (baseStart_443439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_443439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_443439 prefixEnd_443439 := by exact prefixLift 443439
  have htrace : WordTrace (prefixWord ++ tailWord_443439) baseStart_443439 baseEnd_443439 := by
    simpa [prefixWord, tailWord_443439, baseEnd_443439] using wordTrace_append hprefix tailTrace_443439
  have hstable : (prefixWord ++ tailWord_443439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443439).length < 2 ^ (prefixWord ++ tailWord_443439).sum := by decide
  have hdescent : baseEnd_443439 < baseStart_443439 := by decide
  rcases family_descends (prefixWord ++ tailWord_443439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443456 : List Nat := [2, 1, 1, 2, 2, 3, 1, 5, 4]
def baseStart_443456 : Nat := 118140960795 + 443456 * 2 ^ 59
def prefixEnd_443456 : Nat := 4983230072969 + 3 ^ 40 * 443456 * 2
def baseEnd_443456 : Nat := 101202700942365426693595

theorem tailTrace_443456 : CollatzResearch.WordTrace tailWord_443456 prefixEnd_443456 101202700942365426693595 := by
  unfold tailWord_443456
  simp only [CollatzResearch.WordTrace]
  refine ⟨8087084540721061550119111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10782779387628082066825481 8087084540721061550119111)
  ·
    refine ⟨12130626811081592325178667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8087084540721061550119111 12130626811081592325178667)
    ·
      refine ⟨18195940216622388487768001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12130626811081592325178667 18195940216622388487768001)
      ·
        refine ⟨13646955162466791365826001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18195940216622388487768001 13646955162466791365826001)
        ·
          refine ⟨10235216371850093524369501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13646955162466791365826001 10235216371850093524369501)
          ·
            refine ⟨3838206139443785071638563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10235216371850093524369501 3838206139443785071638563)
            ·
              refine ⟨5757309209165677607457845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3838206139443785071638563 5757309209165677607457845)
              ·
                refine ⟨539747738359282275699173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5757309209165677607457845 539747738359282275699173)
                ·
                  refine ⟨101202700942365426693595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 539747738359282275699173 101202700942365426693595)
                  ·
                    rfl

theorem cell21_443456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_443456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_443456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_443456 prefixEnd_443456 := by exact prefixLift 443456
  have htrace : WordTrace (prefixWord ++ tailWord_443456) baseStart_443456 baseEnd_443456 := by
    simpa [prefixWord, tailWord_443456, baseEnd_443456] using wordTrace_append hprefix tailTrace_443456
  have hstable : (prefixWord ++ tailWord_443456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443456).length < 2 ^ (prefixWord ++ tailWord_443456).sum := by decide
  have hdescent : baseEnd_443456 < baseStart_443456 := by decide
  rcases family_descends (prefixWord ++ tailWord_443456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443490 : List Nat := [3, 3, 2, 2, 1, 1, 3, 2, 4]
def baseStart_443490 : Nat := 118140960795 + 443490 * 2 ^ 59
def prefixEnd_443490 : Nat := 4983230072969 + 3 ^ 40 * 443490 * 2
def baseEnd_443490 : Nat := 101210460205588923126859

theorem tailTrace_443490 : CollatzResearch.WordTrace tailWord_443490 prefixEnd_443490 101210460205588923126859 := by
  unfold tailWord_443490
  simp only [CollatzResearch.WordTrace]
  refine ⟨4043852290829736726743981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10783606108879297937983949 4043852290829736726743981)
  ·
    refine ⟨1516444609061151272528993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4043852290829736726743981 1516444609061151272528993)
    ·
      refine ⟨1137333456795863454396745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1516444609061151272528993 1137333456795863454396745)
      ·
        refine ⟨853000092596897590797559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1137333456795863454396745 853000092596897590797559)
        ·
          refine ⟨1279500138895346386196339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853000092596897590797559 1279500138895346386196339)
          ·
            refine ⟨1919250208343019579294509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279500138895346386196339 1919250208343019579294509)
            ·
              refine ⟨719718828128632342235441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1919250208343019579294509 719718828128632342235441)
              ·
                refine ⟨539789121096474256676581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 719718828128632342235441 539789121096474256676581)
                ·
                  refine ⟨101210460205588923126859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 539789121096474256676581 101210460205588923126859)
                  ·
                    rfl

theorem cell21_443490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_443490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_443490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_443490 prefixEnd_443490 := by exact prefixLift 443490
  have htrace : WordTrace (prefixWord ++ tailWord_443490) baseStart_443490 baseEnd_443490 := by
    simpa [prefixWord, tailWord_443490, baseEnd_443490] using wordTrace_append hprefix tailTrace_443490
  have hstable : (prefixWord ++ tailWord_443490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443490).length < 2 ^ (prefixWord ++ tailWord_443490).sum := by decide
  have hdescent : baseEnd_443490 < baseStart_443490 := by decide
  rcases family_descends (prefixWord ++ tailWord_443490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443591 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 8]
def baseStart_443591 : Nat := 118140960795 + 443591 * 2 ^ 59
def prefixEnd_443591 : Nat := 4983230072969 + 3 ^ 40 * 443591 * 2
def baseEnd_443591 : Nat := 101233509781635191943319

theorem tailTrace_443591 : CollatzResearch.WordTrace tailWord_443591 prefixEnd_443591 101233509781635191943319 := by
  unfold tailWord_443591
  simp only [CollatzResearch.WordTrace]
  refine ⟨16179092935953041156402627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10786061957302027437601751 16179092935953041156402627)
  ·
    refine ⟨24268639403929561734603941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16179092935953041156402627 24268639403929561734603941)
    ·
      refine ⟨4550369888236792825238239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24268639403929561734603941 4550369888236792825238239)
      ·
        refine ⟨6825554832355189237857359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4550369888236792825238239 6825554832355189237857359)
        ·
          refine ⟨10238332248532783856786039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6825554832355189237857359 10238332248532783856786039)
          ·
            refine ⟨15357498372799175785179059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10238332248532783856786039 15357498372799175785179059)
            ·
              refine ⟨23036247559198763677768589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15357498372799175785179059 23036247559198763677768589)
              ·
                refine ⟨8638592834699536379163221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23036247559198763677768589 8638592834699536379163221)
                ·
                  refine ⟨101233509781635191943319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8638592834699536379163221 101233509781635191943319)
                  ·
                    rfl

theorem cell21_443591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 8].length) (baseStart_443591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_443591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_443591 prefixEnd_443591 := by exact prefixLift 443591
  have htrace : WordTrace (prefixWord ++ tailWord_443591) baseStart_443591 baseEnd_443591 := by
    simpa [prefixWord, tailWord_443591, baseEnd_443591] using wordTrace_append hprefix tailTrace_443591
  have hstable : (prefixWord ++ tailWord_443591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443591).length < 2 ^ (prefixWord ++ tailWord_443591).sum := by decide
  have hdescent : baseEnd_443591 < baseStart_443591 := by decide
  rcases family_descends (prefixWord ++ tailWord_443591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443597 : List Nat := [1, 6, 2, 2, 2, 8]
def baseStart_443597 : Nat := 118140960795 + 443597 * 2 ^ 59
def prefixEnd_443597 : Nat := 4983230072969 + 3 ^ 40 * 443597 * 2
def baseEnd_443597 : Nat := 3749439965310389438641

theorem tailTrace_443597 : CollatzResearch.WordTrace tailWord_443597 prefixEnd_443597 3749439965310389438641 := by
  unfold tailWord_443597
  simp only [CollatzResearch.WordTrace]
  refine ⟨16179311773931304181121045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10786207849287536120747363 16179311773931304181121045)
  ·
    refine ⟨758405239403029883490049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16179311773931304181121045 758405239403029883490049)
    ·
      refine ⟨568803929552272412617537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 758405239403029883490049 568803929552272412617537)
      ·
        refine ⟨426602947164204309463153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568803929552272412617537 426602947164204309463153)
        ·
          refine ⟨319952210373153232097365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426602947164204309463153 319952210373153232097365)
          ·
            refine ⟨3749439965310389438641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 319952210373153232097365 3749439965310389438641)
            ·
              rfl

theorem cell21_443597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 8].length) (baseStart_443597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_443597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_443597 prefixEnd_443597 := by exact prefixLift 443597
  have htrace : WordTrace (prefixWord ++ tailWord_443597) baseStart_443597 baseEnd_443597 := by
    simpa [prefixWord, tailWord_443597, baseEnd_443597] using wordTrace_append hprefix tailTrace_443597
  have hstable : (prefixWord ++ tailWord_443597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443597).length < 2 ^ (prefixWord ++ tailWord_443597).sum := by decide
  have hdescent : baseEnd_443597 < baseStart_443597 := by decide
  rcases family_descends (prefixWord ++ tailWord_443597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443780 : List Nat := [2, 3, 2, 1, 1, 5, 2, 2, 3]
def baseStart_443780 : Nat := 118140960795 + 443780 * 2 ^ 59
def prefixEnd_443780 : Nat := 4983230072969 + 3 ^ 40 * 443780 * 2
def baseEnd_443780 : Nat := 101276642156612863292933

theorem tailTrace_443780 : CollatzResearch.WordTrace tailWord_443780 prefixEnd_443780 101276642156612863292933 := by
  unfold tailWord_443780
  simp only [CollatzResearch.WordTrace]
  refine ⟨8092993166134163217516397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10790657554845550956688529 8092993166134163217516397)
  ·
    refine ⟨3034872437300311206568649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8092993166134163217516397 3034872437300311206568649)
    ·
      refine ⟨2276154327975233404926487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3034872437300311206568649 2276154327975233404926487)
      ·
        refine ⟨3414231491962850107389731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2276154327975233404926487 3414231491962850107389731)
        ·
          refine ⟨5121347237944275161084597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3414231491962850107389731 5121347237944275161084597)
          ·
            refine ⟨480126303557275796351681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5121347237944275161084597 480126303557275796351681)
            ·
              refine ⟨360094727667956847263761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480126303557275796351681 360094727667956847263761)
              ·
                refine ⟨270071045750967635447821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360094727667956847263761 270071045750967635447821)
                ·
                  refine ⟨101276642156612863292933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270071045750967635447821 101276642156612863292933)
                  ·
                    rfl

theorem cell21_443780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_443780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_443780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_443780 prefixEnd_443780 := by exact prefixLift 443780
  have htrace : WordTrace (prefixWord ++ tailWord_443780) baseStart_443780 baseEnd_443780 := by
    simpa [prefixWord, tailWord_443780, baseEnd_443780] using wordTrace_append hprefix tailTrace_443780
  have hstable : (prefixWord ++ tailWord_443780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443780).length < 2 ^ (prefixWord ++ tailWord_443780).sum := by decide
  have hdescent : baseEnd_443780 < baseStart_443780 := by decide
  rcases family_descends (prefixWord ++ tailWord_443780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443805 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 7]
def baseStart_443805 : Nat := 118140960795 + 443805 * 2 ^ 59
def prefixEnd_443805 : Nat := 4983230072969 + 3 ^ 40 * 443805 * 2
def baseEnd_443805 : Nat := 101282347497218375376215

theorem tailTrace_443805 : CollatzResearch.WordTrace tailWord_443805 prefixEnd_443805 101282347497218375376215 := by
  unfold tailWord_443805
  simp only [CollatzResearch.WordTrace]
  refine ⟨16186898157177755704692869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10791265438118503803128579 16186898157177755704692869)
  ·
    refine ⟨3035043404470829194629913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16186898157177755704692869 3035043404470829194629913)
    ·
      refine ⟨2276282553353121895972435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3035043404470829194629913 2276282553353121895972435)
      ·
        refine ⟨3414423830029682843958653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2276282553353121895972435 3414423830029682843958653)
        ·
          refine ⟨1280408936261131066484495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3414423830029682843958653 1280408936261131066484495)
          ·
            refine ⟨1920613404391696599726743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280408936261131066484495 1920613404391696599726743)
            ·
              refine ⟨2880920106587544899590115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1920613404391696599726743 2880920106587544899590115)
              ·
                refine ⟨4321380159881317349385173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2880920106587544899590115 4321380159881317349385173)
                ·
                  refine ⟨101282347497218375376215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4321380159881317349385173 101282347497218375376215)
                  ·
                    rfl

theorem cell21_443805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_443805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_443805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_443805 prefixEnd_443805 := by exact prefixLift 443805
  have htrace : WordTrace (prefixWord ++ tailWord_443805) baseStart_443805 baseEnd_443805 := by
    simpa [prefixWord, tailWord_443805, baseEnd_443805] using wordTrace_append hprefix tailTrace_443805
  have hstable : (prefixWord ++ tailWord_443805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443805).length < 2 ^ (prefixWord ++ tailWord_443805).sum := by decide
  have hdescent : baseEnd_443805 < baseStart_443805 := by decide
  rcases family_descends (prefixWord ++ tailWord_443805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444005 : List Nat := [1, 3, 1, 3, 3, 3, 1, 2, 4]
def baseStart_444005 : Nat := 118140960795 + 444005 * 2 ^ 59
def prefixEnd_444005 : Nat := 4983230072969 + 3 ^ 40 * 444005 * 2
def baseEnd_444005 : Nat := 101327990222062472042473

theorem tailTrace_444005 : CollatzResearch.WordTrace tailWord_444005 prefixEnd_444005 101327990222062472042473 := by
  unfold tailWord_444005
  simp only [CollatzResearch.WordTrace]
  refine ⟨16194192756453189861973469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10796128504302126574648979 16194192756453189861973469)
  ·
    refine ⟨6072822283669946198240051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16194192756453189861973469 6072822283669946198240051)
    ·
      refine ⟨9109233425504919297360077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6072822283669946198240051 9109233425504919297360077)
      ·
        refine ⟨3415962534564344736510029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9109233425504919297360077 3415962534564344736510029)
        ·
          refine ⟨1280985950461629276191261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3415962534564344736510029 1280985950461629276191261)
          ·
            refine ⟨480369731423110978571723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1280985950461629276191261 480369731423110978571723)
            ·
              refine ⟨720554597134666467857585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480369731423110978571723 720554597134666467857585)
              ·
                refine ⟨540415947850999850893189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 720554597134666467857585 540415947850999850893189)
                ·
                  refine ⟨101327990222062472042473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 540415947850999850893189 101327990222062472042473)
                  ·
                    rfl

theorem cell21_444005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_444005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444005 prefixEnd_444005 := by exact prefixLift 444005
  have htrace : WordTrace (prefixWord ++ tailWord_444005) baseStart_444005 baseEnd_444005 := by
    simpa [prefixWord, tailWord_444005, baseEnd_444005] using wordTrace_append hprefix tailTrace_444005
  have hstable : (prefixWord ++ tailWord_444005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444005).length < 2 ^ (prefixWord ++ tailWord_444005).sum := by decide
  have hdescent : baseEnd_444005 < baseStart_444005 := by decide
  rcases family_descends (prefixWord ++ tailWord_444005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444022 : List Nat := [5, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_444022 : Nat := 118140960795 + 444022 * 2 ^ 59
def prefixEnd_444022 : Nat := 4983230072969 + 3 ^ 40 * 444022 * 2
def baseEnd_444022 : Nat := 101331869853674220259105

theorem tailTrace_444022 : CollatzResearch.WordTrace tailWord_444022 prefixEnd_444022 101331869853674220259105 := by
  unfold tailWord_444022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1012175799836975110333895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10796541864927734510228213 1012175799836975110333895)
  ·
    refine ⟨1518263699755462665500843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1012175799836975110333895 1518263699755462665500843)
    ·
      refine ⟨2277395549633193998251265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1518263699755462665500843 2277395549633193998251265)
      ·
        refine ⟨1708046662224895498688449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2277395549633193998251265 1708046662224895498688449)
        ·
          refine ⟨1281034996668671624016337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1708046662224895498688449 1281034996668671624016337)
          ·
            refine ⟨960776247501503718012253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1281034996668671624016337 960776247501503718012253)
            ·
              refine ⟨360291092813063894254595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 960776247501503718012253 360291092813063894254595)
              ·
                refine ⟨540436639219595841381893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360291092813063894254595 540436639219595841381893)
                ·
                  refine ⟨101331869853674220259105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 540436639219595841381893 101331869853674220259105)
                  ·
                    rfl

theorem cell21_444022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_444022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444022 prefixEnd_444022 := by exact prefixLift 444022
  have htrace : WordTrace (prefixWord ++ tailWord_444022) baseStart_444022 baseEnd_444022 := by
    simpa [prefixWord, tailWord_444022, baseEnd_444022] using wordTrace_append hprefix tailTrace_444022
  have hstable : (prefixWord ++ tailWord_444022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444022).length < 2 ^ (prefixWord ++ tailWord_444022).sum := by decide
  have hdescent : baseEnd_444022 < baseStart_444022 := by decide
  rcases family_descends (prefixWord ++ tailWord_444022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444033 : List Nat := [1, 2, 4, 2, 1, 2, 2, 2, 5]
def baseStart_444033 : Nat := 118140960795 + 444033 * 2 ^ 59
def prefixEnd_444033 : Nat := 4983230072969 + 3 ^ 40 * 444033 * 2
def baseEnd_444033 : Nat := 101334380203540645575749

theorem tailTrace_444033 : CollatzResearch.WordTrace tailWord_444033 prefixEnd_444033 101334380203540645575749 := by
  unfold tailWord_444033
  simp only [CollatzResearch.WordTrace]
  refine ⟨16195214000351750643992753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10796809333567833762661835 16195214000351750643992753)
  ·
    refine ⟨12146410500263812982994565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16195214000351750643992753 12146410500263812982994565)
    ·
      refine ⟨2277451968799464934311481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12146410500263812982994565 2277451968799464934311481)
      ·
        refine ⟨1708088976599598700733611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2277451968799464934311481 1708088976599598700733611)
        ·
          refine ⟨2562133464899398051100417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1708088976599598700733611 2562133464899398051100417)
          ·
            refine ⟨1921600098674548538325313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2562133464899398051100417 1921600098674548538325313)
            ·
              refine ⟨1441200074005911403743985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1921600098674548538325313 1441200074005911403743985)
              ·
                refine ⟨1080900055504433552807989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1441200074005911403743985 1080900055504433552807989)
                ·
                  refine ⟨101334380203540645575749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1080900055504433552807989 101334380203540645575749)
                  ·
                    rfl

theorem cell21_444033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_444033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444033 prefixEnd_444033 := by exact prefixLift 444033
  have htrace : WordTrace (prefixWord ++ tailWord_444033) baseStart_444033 baseEnd_444033 := by
    simpa [prefixWord, tailWord_444033, baseEnd_444033] using wordTrace_append hprefix tailTrace_444033
  have hstable : (prefixWord ++ tailWord_444033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444033).length < 2 ^ (prefixWord ++ tailWord_444033).sum := by decide
  have hdescent : baseEnd_444033 < baseStart_444033 := by decide
  rcases family_descends (prefixWord ++ tailWord_444033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444036 : List Nat := [2, 3, 2, 1, 4, 2, 2, 5]
def baseStart_444036 : Nat := 118140960795 + 444036 * 2 ^ 59
def prefixEnd_444036 : Nat := 4983230072969 + 3 ^ 40 * 444036 * 2
def baseEnd_444036 : Nat := 33778354948137769008581

theorem tailTrace_444036 : CollatzResearch.WordTrace tailWord_444036 prefixEnd_444036 33778354948137769008581 := by
  unfold tailWord_444036
  simp only [CollatzResearch.WordTrace]
  refine ⟨8097661709670441078175981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10796882279560588104234641 8097661709670441078175981)
  ·
    refine ⟨3036623141126415404315993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8097661709670441078175981 3036623141126415404315993)
    ·
      refine ⟨2277467355844811553236995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3036623141126415404315993 2277467355844811553236995)
      ·
        refine ⟨3416201033767217329855493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2277467355844811553236995 3416201033767217329855493)
        ·
          refine ⟨640537693831353249347905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3416201033767217329855493 640537693831353249347905)
          ·
            refine ⟨480403270373514937010929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640537693831353249347905 480403270373514937010929)
            ·
              refine ⟨360302452780136202758197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480403270373514937010929 360302452780136202758197)
              ·
                refine ⟨33778354948137769008581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 360302452780136202758197 33778354948137769008581)
                ·
                  rfl

theorem cell21_444036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 5].length) (baseStart_444036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444036 prefixEnd_444036 := by exact prefixLift 444036
  have htrace : WordTrace (prefixWord ++ tailWord_444036) baseStart_444036 baseEnd_444036 := by
    simpa [prefixWord, tailWord_444036, baseEnd_444036] using wordTrace_append hprefix tailTrace_444036
  have hstable : (prefixWord ++ tailWord_444036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444036).length < 2 ^ (prefixWord ++ tailWord_444036).sum := by decide
  have hdescent : baseEnd_444036 < baseStart_444036 := by decide
  rcases family_descends (prefixWord ++ tailWord_444036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444118 : List Nat := [5, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_444118 : Nat := 118140960795 + 444118 * 2 ^ 59
def prefixEnd_444118 : Nat := 4983230072969 + 3 ^ 40 * 444118 * 2
def baseEnd_444118 : Nat := 101353778361599386658909

theorem tailTrace_444118 : CollatzResearch.WordTrace tailWord_444118 prefixEnd_444118 101353778361599386658909 := by
  unfold tailWord_444118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1012394637815238135052313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10798876136695873440558005 1012394637815238135052313)
  ·
    refine ⟨759295978361428601289235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1012394637815238135052313 759295978361428601289235)
    ·
      refine ⟨1138943967542142901933853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 759295978361428601289235 1138943967542142901933853)
      ·
        refine ⟨427103987828303588225195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1138943967542142901933853 427103987828303588225195)
        ·
          refine ⟨640655981742455382337793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427103987828303588225195 640655981742455382337793)
          ·
            refine ⟨480491986306841536753345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640655981742455382337793 480491986306841536753345)
            ·
              refine ⟨360368989730131152565009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480491986306841536753345 360368989730131152565009)
              ·
                refine ⟨270276742297598364423757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360368989730131152565009 270276742297598364423757)
                ·
                  refine ⟨101353778361599386658909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270276742297598364423757 101353778361599386658909)
                  ·
                    rfl

theorem cell21_444118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_444118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444118 prefixEnd_444118 := by exact prefixLift 444118
  have htrace : WordTrace (prefixWord ++ tailWord_444118) baseStart_444118 baseEnd_444118 := by
    simpa [prefixWord, tailWord_444118, baseEnd_444118] using wordTrace_append hprefix tailTrace_444118
  have hstable : (prefixWord ++ tailWord_444118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444118).length < 2 ^ (prefixWord ++ tailWord_444118).sum := by decide
  have hdescent : baseEnd_444118 < baseStart_444118 := by decide
  rcases family_descends (prefixWord ++ tailWord_444118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444166 : List Nat := [6, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_444166 : Nat := 118140960795 + 444166 * 2 ^ 59
def prefixEnd_444166 : Nat := 4983230072969 + 3 ^ 40 * 444166 * 2
def baseEnd_444166 : Nat := 101364732615561969858811

theorem tailTrace_444166 : CollatzResearch.WordTrace tailWord_444166 prefixEnd_444166 101364732615561969858811 := by
  unfold tailWord_444166
  simp only [CollatzResearch.WordTrace]
  refine ⟨506252028402184823705761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10800043272579942905722901 506252028402184823705761)
  ·
    refine ⟨379689021301638617779321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 506252028402184823705761 379689021301638617779321)
    ·
      refine ⟨284766765976228963334491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379689021301638617779321 284766765976228963334491)
      ·
        refine ⟨427150148964343445001737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284766765976228963334491 427150148964343445001737)
        ·
          refine ⟨320362611723257583751303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427150148964343445001737 320362611723257583751303)
          ·
            refine ⟨480543917584886375626955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320362611723257583751303 480543917584886375626955)
            ·
              refine ⟨720815876377329563440433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480543917584886375626955 720815876377329563440433)
              ·
                refine ⟨540611907282997172580325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 720815876377329563440433 540611907282997172580325)
                ·
                  refine ⟨101364732615561969858811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 540611907282997172580325 101364732615561969858811)
                  ·
                    rfl

theorem cell21_444166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_444166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444166 prefixEnd_444166 := by exact prefixLift 444166
  have htrace : WordTrace (prefixWord ++ tailWord_444166) baseStart_444166 baseEnd_444166 := by
    simpa [prefixWord, tailWord_444166, baseEnd_444166] using wordTrace_append hprefix tailTrace_444166
  have hstable : (prefixWord ++ tailWord_444166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444166).length < 2 ^ (prefixWord ++ tailWord_444166).sum := by decide
  have hdescent : baseEnd_444166 < baseStart_444166 := by decide
  rcases family_descends (prefixWord ++ tailWord_444166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444168 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 7]
def baseStart_444168 : Nat := 118140960795 + 444168 * 2 ^ 59
def prefixEnd_444168 : Nat := 4983230072969 + 3 ^ 40 * 444168 * 2
def baseEnd_444168 : Nat := 101365189042810410825473

theorem tailTrace_444168 : CollatzResearch.WordTrace tailWord_444168 prefixEnd_444168 101365189042810410825473 := by
  unfold tailWord_444168
  simp only [CollatzResearch.WordTrace]
  refine ⟨8100068927431334350078579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10800091903241779133438105 8100068927431334350078579)
  ·
    refine ⟨12150103391147001525117869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8100068927431334350078579 12150103391147001525117869)
    ·
      refine ⟨4556288771680125571919201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12150103391147001525117869 4556288771680125571919201)
      ·
        refine ⟨3417216578760094178939401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4556288771680125571919201 3417216578760094178939401)
        ·
          refine ⟨2562912434070070634204551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3417216578760094178939401 2562912434070070634204551)
          ·
            refine ⟨3844368651105105951306827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2562912434070070634204551 3844368651105105951306827)
            ·
              refine ⟨5766552976657658926960241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3844368651105105951306827 5766552976657658926960241)
              ·
                refine ⟨4324914732493244195220181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5766552976657658926960241 4324914732493244195220181)
                ·
                  refine ⟨101365189042810410825473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4324914732493244195220181 101365189042810410825473)
                  ·
                    rfl

theorem cell21_444168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_444168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444168 prefixEnd_444168 := by exact prefixLift 444168
  have htrace : WordTrace (prefixWord ++ tailWord_444168) baseStart_444168 baseEnd_444168 := by
    simpa [prefixWord, tailWord_444168, baseEnd_444168] using wordTrace_append hprefix tailTrace_444168
  have hstable : (prefixWord ++ tailWord_444168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444168).length < 2 ^ (prefixWord ++ tailWord_444168).sum := by decide
  have hdescent : baseEnd_444168 < baseStart_444168 := by decide
  rcases family_descends (prefixWord ++ tailWord_444168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444413 : List Nat := [1, 4, 1, 1, 1, 2, 2, 6, 3]
def baseStart_444413 : Nat := 118140960795 + 444413 * 2 ^ 59
def prefixEnd_444413 : Nat := 4983230072969 + 3 ^ 40 * 444413 * 2
def baseEnd_444413 : Nat := 101421101380744429241639

theorem tailTrace_444413 : CollatzResearch.WordTrace tailWord_444413 prefixEnd_444413 101421101380744429241639 := by
  unfold tailWord_444413
  simp only [CollatzResearch.WordTrace]
  refine ⟨16209073738975075542825893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10806049159316717028550595 16209073738975075542825893)
  ·
    refine ⟨3039201326057826664279855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16209073738975075542825893 3039201326057826664279855)
    ·
      refine ⟨4558801989086739996419783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3039201326057826664279855 4558801989086739996419783)
      ·
        refine ⟨6838202983630109994629675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4558801989086739996419783 6838202983630109994629675)
        ·
          refine ⟨10257304475445164991944513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6838202983630109994629675 10257304475445164991944513)
          ·
            refine ⟨7692978356583873743958385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10257304475445164991944513 7692978356583873743958385)
            ·
              refine ⟨5769733767437905307968789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7692978356583873743958385 5769733767437905307968789)
              ·
                refine ⟨270456270348651811311037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5769733767437905307968789 270456270348651811311037)
                ·
                  refine ⟨101421101380744429241639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270456270348651811311037 101421101380744429241639)
                  ·
                    rfl

theorem cell21_444413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_444413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444413 prefixEnd_444413 := by exact prefixLift 444413
  have htrace : WordTrace (prefixWord ++ tailWord_444413) baseStart_444413 baseEnd_444413 := by
    simpa [prefixWord, tailWord_444413, baseEnd_444413] using wordTrace_append hprefix tailTrace_444413
  have hstable : (prefixWord ++ tailWord_444413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444413).length < 2 ^ (prefixWord ++ tailWord_444413).sum := by decide
  have hdescent : baseEnd_444413 < baseStart_444413 := by decide
  rcases family_descends (prefixWord ++ tailWord_444413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444427 : List Nat := [1, 1, 1, 1, 6, 1, 3, 3, 4]
def baseStart_444427 : Nat := 118140960795 + 444427 * 2 ^ 59
def prefixEnd_444427 : Nat := 4983230072969 + 3 ^ 40 * 444427 * 2
def baseEnd_444427 : Nat := 101424296371483516008277

theorem tailTrace_444427 : CollatzResearch.WordTrace tailWord_444427 prefixEnd_444427 101424296371483516008277 := by
  unfold tailWord_444427
  simp only [CollatzResearch.WordTrace]
  refine ⟨16209584360924355933835535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10806389573949570622557023 16209584360924355933835535)
  ·
    refine ⟨24314376541386533900753303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16209584360924355933835535 24314376541386533900753303)
    ·
      refine ⟨36471564812079800851129955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24314376541386533900753303 36471564812079800851129955)
      ·
        refine ⟨54707347218119701276694933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36471564812079800851129955 54707347218119701276694933)
        ·
          refine ⟨2564406900849360997345075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54707347218119701276694933 2564406900849360997345075)
          ·
            refine ⟨3846610351274041496017613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2564406900849360997345075 3846610351274041496017613)
            ·
              refine ⟨1442478881727765561006605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3846610351274041496017613 1442478881727765561006605)
              ·
                refine ⟨540929580647912085377477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1442478881727765561006605 540929580647912085377477)
                ·
                  refine ⟨101424296371483516008277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 540929580647912085377477 101424296371483516008277)
                  ·
                    rfl

theorem cell21_444427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 4].length) (baseStart_444427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444427 prefixEnd_444427 := by exact prefixLift 444427
  have htrace : WordTrace (prefixWord ++ tailWord_444427) baseStart_444427 baseEnd_444427 := by
    simpa [prefixWord, tailWord_444427, baseEnd_444427] using wordTrace_append hprefix tailTrace_444427
  have hstable : (prefixWord ++ tailWord_444427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444427).length < 2 ^ (prefixWord ++ tailWord_444427).sum := by decide
  have hdescent : baseEnd_444427 < baseStart_444427 := by decide
  rcases family_descends (prefixWord ++ tailWord_444427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444517 : List Nat := [1, 3, 1, 3, 2, 3, 8]
def baseStart_444517 : Nat := 118140960795 + 444517 * 2 ^ 59
def prefixEnd_444517 : Nat := 4983230072969 + 3 ^ 40 * 444517 * 2
def baseEnd_444517 : Nat := 11271648399740373278677

theorem tailTrace_444517 : CollatzResearch.WordTrace tailWord_444517 prefixEnd_444517 11271648399740373278677 := by
  unfold tailWord_444517
  simp only [CollatzResearch.WordTrace]
  refine ⟨16212866930598301304611805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10808577953732200869741203 16212866930598301304611805)
  ·
    refine ⟨6079825098974362989229427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16212866930598301304611805 6079825098974362989229427)
    ·
      refine ⟨9119737648461544483844141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6079825098974362989229427 9119737648461544483844141)
      ·
        refine ⟨3419901618173079181441553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9119737648461544483844141 3419901618173079181441553)
        ·
          refine ⟨2564926213629809386081165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3419901618173079181441553 2564926213629809386081165)
          ·
            refine ⟨961847330111178519780437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2564926213629809386081165 961847330111178519780437)
            ·
              refine ⟨11271648399740373278677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 961847330111178519780437 11271648399740373278677)
              ·
                rfl

theorem cell21_444517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 8].length) (baseStart_444517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444517 prefixEnd_444517 := by exact prefixLift 444517
  have htrace : WordTrace (prefixWord ++ tailWord_444517) baseStart_444517 baseEnd_444517 := by
    simpa [prefixWord, tailWord_444517, baseEnd_444517] using wordTrace_append hprefix tailTrace_444517
  have hstable : (prefixWord ++ tailWord_444517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444517).length < 2 ^ (prefixWord ++ tailWord_444517).sum := by decide
  have hdescent : baseEnd_444517 < baseStart_444517 := by decide
  rcases family_descends (prefixWord ++ tailWord_444517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444548 : List Nat := [2, 3, 2, 1, 2, 1, 1, 4, 5]
def baseStart_444548 : Nat := 118140960795 + 444548 * 2 ^ 59
def prefixEnd_444548 : Nat := 4983230072969 + 3 ^ 40 * 444548 * 2
def baseEnd_444548 : Nat := 101451910220014194491363

theorem tailTrace_444548 : CollatzResearch.WordTrace tailWord_444548 prefixEnd_444548 101451910220014194491363 := by
  unfold tailWord_444548
  simp only [CollatzResearch.WordTrace]
  refine ⟨8106998796742996799495149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10809331728990662399326865 8106998796742996799495149)
  ·
    refine ⟨3040124548778623799810681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8106998796742996799495149 3040124548778623799810681)
    ·
      refine ⟨2280093411583967849858011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3040124548778623799810681 2280093411583967849858011)
      ·
        refine ⟨3420140117375951774787017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2280093411583967849858011 3420140117375951774787017)
        ·
          refine ⟨2565105088031963831090263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3420140117375951774787017 2565105088031963831090263)
          ·
            refine ⟨3847657632047945746635395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2565105088031963831090263 3847657632047945746635395)
            ·
              refine ⟨5771486448071918619953093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3847657632047945746635395 5771486448071918619953093)
              ·
                refine ⟨1082153709013484741241205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5771486448071918619953093 1082153709013484741241205)
                ·
                  refine ⟨101451910220014194491363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1082153709013484741241205 101451910220014194491363)
                  ·
                    rfl

theorem cell21_444548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_444548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444548 prefixEnd_444548 := by exact prefixLift 444548
  have htrace : WordTrace (prefixWord ++ tailWord_444548) baseStart_444548 baseEnd_444548 := by
    simpa [prefixWord, tailWord_444548, baseEnd_444548] using wordTrace_append hprefix tailTrace_444548
  have hstable : (prefixWord ++ tailWord_444548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444548).length < 2 ^ (prefixWord ++ tailWord_444548).sum := by decide
  have hdescent : baseEnd_444548 < baseStart_444548 := by decide
  rcases family_descends (prefixWord ++ tailWord_444548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444607 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 7]
def baseStart_444607 : Nat := 118140960795 + 444607 * 2 ^ 59
def prefixEnd_444607 : Nat := 4983230072969 + 3 ^ 40 * 444607 * 2
def baseEnd_444607 : Nat := 101465374823843203007909

theorem tailTrace_444607 : CollatzResearch.WordTrace tailWord_444607 prefixEnd_444607 101465374823843203007909 := by
  unfold tailWord_444607
  simp only [CollatzResearch.WordTrace]
  refine ⟨16216149500272246675388075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10810766333514831116925383 16216149500272246675388075)
  ·
    refine ⟨24324224250408370013082113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16216149500272246675388075 24324224250408370013082113)
    ·
      refine ⟨18243168187806277509811585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24324224250408370013082113 18243168187806277509811585)
      ·
        refine ⟨13682376140854708132358689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18243168187806277509811585 13682376140854708132358689)
        ·
          refine ⟨10261782105641031099269017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13682376140854708132358689 10261782105641031099269017)
          ·
            refine ⟨7696336579230773324451763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10261782105641031099269017 7696336579230773324451763)
            ·
              refine ⟨11544504868846159986677645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7696336579230773324451763 11544504868846159986677645)
              ·
                refine ⟨4329189325817309995004117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11544504868846159986677645 4329189325817309995004117)
                ·
                  refine ⟨101465374823843203007909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4329189325817309995004117 101465374823843203007909)
                  ·
                    rfl

theorem cell21_444607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 7].length) (baseStart_444607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444607 prefixEnd_444607 := by exact prefixLift 444607
  have htrace : WordTrace (prefixWord ++ tailWord_444607) baseStart_444607 baseEnd_444607 := by
    simpa [prefixWord, tailWord_444607, baseEnd_444607] using wordTrace_append hprefix tailTrace_444607
  have hstable : (prefixWord ++ tailWord_444607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444607).length < 2 ^ (prefixWord ++ tailWord_444607).sum := by decide
  have hdescent : baseEnd_444607 < baseStart_444607 := by decide
  rcases family_descends (prefixWord ++ tailWord_444607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444641 : List Nat := [1, 2, 3, 1, 3, 1, 3, 4, 3]
def baseStart_444641 : Nat := 118140960795 + 444641 * 2 ^ 59
def prefixEnd_444641 : Nat := 4983230072969 + 3 ^ 40 * 444641 * 2
def baseEnd_444641 : Nat := 101473134087066699441173

theorem tailTrace_444641 : CollatzResearch.WordTrace tailWord_444641 prefixEnd_444641 101473134087066699441173 := by
  unfold tailWord_444641
  simp only [CollatzResearch.WordTrace]
  refine ⟨16217389582149070482125777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10811593054766046988083851 16217389582149070482125777)
  ·
    refine ⟨12163042186611802861594333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16217389582149070482125777 12163042186611802861594333)
    ·
      refine ⟨4561140819979426073097875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12163042186611802861594333 4561140819979426073097875)
      ·
        refine ⟨6841711229969139109646813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4561140819979426073097875 6841711229969139109646813)
        ·
          refine ⟨2565641711238427166117555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6841711229969139109646813 2565641711238427166117555)
          ·
            refine ⟨3848462566857640749176333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2565641711238427166117555 3848462566857640749176333)
            ·
              refine ⟨1443173462571615280941125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3848462566857640749176333 1443173462571615280941125)
              ·
                refine ⟨270595024232177865176461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1443173462571615280941125 270595024232177865176461)
                ·
                  refine ⟨101473134087066699441173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270595024232177865176461 101473134087066699441173)
                  ·
                    rfl

theorem cell21_444641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 3].length) (baseStart_444641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444641 prefixEnd_444641 := by exact prefixLift 444641
  have htrace : WordTrace (prefixWord ++ tailWord_444641) baseStart_444641 baseEnd_444641 := by
    simpa [prefixWord, tailWord_444641, baseEnd_444641] using wordTrace_append hprefix tailTrace_444641
  have hstable : (prefixWord ++ tailWord_444641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444641).length < 2 ^ (prefixWord ++ tailWord_444641).sum := by decide
  have hdescent : baseEnd_444641 < baseStart_444641 := by decide
  rcases family_descends (prefixWord ++ tailWord_444641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444655 : List Nat := [1, 1, 2, 1, 6, 1, 2, 3, 4]
def baseStart_444655 : Nat := 118140960795 + 444655 * 2 ^ 59
def prefixEnd_444655 : Nat := 4983230072969 + 3 ^ 40 * 444655 * 2
def baseEnd_444655 : Nat := 101476329077805786207811

theorem tailTrace_444655 : CollatzResearch.WordTrace tailWord_444655 prefixEnd_444655 101476329077805786207811 := by
  unfold tailWord_444655
  simp only [CollatzResearch.WordTrace]
  refine ⟨16217900204098350873135419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10811933469398900582090279 16217900204098350873135419)
  ·
    refine ⟨24326850306147526309703129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16217900204098350873135419 24326850306147526309703129)
    ·
      refine ⟨18245137729610644732277347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24326850306147526309703129 18245137729610644732277347)
      ·
        refine ⟨27367706594415967098416021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18245137729610644732277347 27367706594415967098416021)
        ·
          refine ⟨1282861246613248457738251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27367706594415967098416021 1282861246613248457738251)
          ·
            refine ⟨1924291869919872686607377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282861246613248457738251 1924291869919872686607377)
            ·
              refine ⟨1443218902439904514955533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1924291869919872686607377 1443218902439904514955533)
              ·
                refine ⟨541207088414964193108325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1443218902439904514955533 541207088414964193108325)
                ·
                  refine ⟨101476329077805786207811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 541207088414964193108325 101476329077805786207811)
                  ·
                    rfl

theorem cell21_444655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 4].length) (baseStart_444655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444655 prefixEnd_444655 := by exact prefixLift 444655
  have htrace : WordTrace (prefixWord ++ tailWord_444655) baseStart_444655 baseEnd_444655 := by
    simpa [prefixWord, tailWord_444655, baseEnd_444655] using wordTrace_append hprefix tailTrace_444655
  have hstable : (prefixWord ++ tailWord_444655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444655).length < 2 ^ (prefixWord ++ tailWord_444655).sum := by decide
  have hdescent : baseEnd_444655 < baseStart_444655 := by decide
  rcases family_descends (prefixWord ++ tailWord_444655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444683 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 7]
def baseStart_444683 : Nat := 118140960795 + 444683 * 2 ^ 59
def prefixEnd_444683 : Nat := 4983230072969 + 3 ^ 40 * 444683 * 2
def baseEnd_444683 : Nat := 101482719059283959741087

theorem tailTrace_444683 : CollatzResearch.WordTrace tailWord_444683 prefixEnd_444683 101482719059283959741087 := by
  unfold tailWord_444683
  simp only [CollatzResearch.WordTrace]
  refine ⟨16218921447996911655154703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10812614298664607770103135 16218921447996911655154703)
  ·
    refine ⟨24328382171995367482732055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16218921447996911655154703 24328382171995367482732055)
    ·
      refine ⟨36492573257993051224098083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24328382171995367482732055 36492573257993051224098083)
      ·
        refine ⟨54738859886989576836147125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36492573257993051224098083 54738859886989576836147125)
        ·
          refine ⟨5131768114405272828388793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54738859886989576836147125 5131768114405272828388793)
          ·
            refine ⟨3848826085803954621291595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5131768114405272828388793 3848826085803954621291595)
            ·
              refine ⟨5773239128705931931937393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3848826085803954621291595 5773239128705931931937393)
              ·
                refine ⟨4329929346529448948953045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5773239128705931931937393 4329929346529448948953045)
                ·
                  refine ⟨101482719059283959741087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4329929346529448948953045 101482719059283959741087)
                  ·
                    rfl

theorem cell21_444683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 7].length) (baseStart_444683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444683 prefixEnd_444683 := by exact prefixLift 444683
  have htrace : WordTrace (prefixWord ++ tailWord_444683) baseStart_444683 baseEnd_444683 := by
    simpa [prefixWord, tailWord_444683, baseEnd_444683] using wordTrace_append hprefix tailTrace_444683
  have hstable : (prefixWord ++ tailWord_444683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444683).length < 2 ^ (prefixWord ++ tailWord_444683).sum := by decide
  have hdescent : baseEnd_444683 < baseStart_444683 := by decide
  rcases family_descends (prefixWord ++ tailWord_444683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444734 : List Nat := [4, 2, 1, 2, 1, 2, 3, 3, 3]
def baseStart_444734 : Nat := 118140960795 + 444734 * 2 ^ 59
def prefixEnd_444734 : Nat := 4983230072969 + 3 ^ 40 * 444734 * 2
def baseEnd_444734 : Nat := 101494357954119204390983

theorem tailTrace_444734 : CollatzResearch.WordTrace tailWord_444734 prefixEnd_444734 101494357954119204390983 := by
  unfold tailWord_444734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2027597696351518420657657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10813854380541431576840837 2027597696351518420657657)
  ·
    refine ⟨1520698272263638815493243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2027597696351518420657657 1520698272263638815493243)
    ·
      refine ⟨2281047408395458223239865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1520698272263638815493243 2281047408395458223239865)
      ·
        refine ⟨1710785556296593667429899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2281047408395458223239865 1710785556296593667429899)
        ·
          refine ⟨2566178334444890501144849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1710785556296593667429899 2566178334444890501144849)
          ·
            refine ⟨1924633750833667875858637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2566178334444890501144849 1924633750833667875858637)
            ·
              refine ⟨721737656562625453446989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1924633750833667875858637 721737656562625453446989)
              ·
                refine ⟨270651621210984545042621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 721737656562625453446989 270651621210984545042621)
                ·
                  refine ⟨101494357954119204390983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270651621210984545042621 101494357954119204390983)
                  ·
                    rfl

theorem cell21_444734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_444734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444734 prefixEnd_444734 := by exact prefixLift 444734
  have htrace : WordTrace (prefixWord ++ tailWord_444734) baseStart_444734 baseEnd_444734 := by
    simpa [prefixWord, tailWord_444734, baseEnd_444734] using wordTrace_append hprefix tailTrace_444734
  have hstable : (prefixWord ++ tailWord_444734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444734).length < 2 ^ (prefixWord ++ tailWord_444734).sum := by decide
  have hdescent : baseEnd_444734 < baseStart_444734 := by decide
  rcases family_descends (prefixWord ++ tailWord_444734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444807 : List Nat := [1, 1, 4, 2, 2, 1, 4, 2, 4]
def baseStart_444807 : Nat := 118140960795 + 444807 * 2 ^ 59
def prefixEnd_444807 : Nat := 4983230072969 + 3 ^ 40 * 444807 * 2
def baseEnd_444807 : Nat := 101511017548687299674167

theorem tailTrace_444807 : CollatzResearch.WordTrace tailWord_444807 prefixEnd_444807 101511017548687299674167 := by
  unfold tailWord_444807
  simp only [CollatzResearch.WordTrace]
  refine ⟨16223444099547680832668675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10815629399698453888445783 16223444099547680832668675)
  ·
    refine ⟨24335166149321521249003013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16223444099547680832668675 24335166149321521249003013)
    ·
      refine ⟨4562843652997785234188065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24335166149321521249003013 4562843652997785234188065)
      ·
        refine ⟨3422132739748338925641049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4562843652997785234188065 3422132739748338925641049)
        ·
          refine ⟨2566599554811254194230787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3422132739748338925641049 2566599554811254194230787)
          ·
            refine ⟨3849899332216881291346181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566599554811254194230787 3849899332216881291346181)
            ·
              refine ⟨721856124790665242127409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3849899332216881291346181 721856124790665242127409)
              ·
                refine ⟨541392093592998931595557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 721856124790665242127409 541392093592998931595557)
                ·
                  refine ⟨101511017548687299674167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 541392093592998931595557 101511017548687299674167)
                  ·
                    rfl

theorem cell21_444807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 4].length) (baseStart_444807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444807 prefixEnd_444807 := by exact prefixLift 444807
  have htrace : WordTrace (prefixWord ++ tailWord_444807) baseStart_444807 baseEnd_444807 := by
    simpa [prefixWord, tailWord_444807, baseEnd_444807] using wordTrace_append hprefix tailTrace_444807
  have hstable : (prefixWord ++ tailWord_444807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444807).length < 2 ^ (prefixWord ++ tailWord_444807).sum := by decide
  have hdescent : baseEnd_444807 < baseStart_444807 := by decide
  rcases family_descends (prefixWord ++ tailWord_444807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444835 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 7]
def baseStart_444835 : Nat := 118140960795 + 444835 * 2 ^ 59
def prefixEnd_444835 : Nat := 4983230072969 + 3 ^ 40 * 444835 * 2
def baseEnd_444835 : Nat := 101517407530165473207443

theorem tailTrace_444835 : CollatzResearch.WordTrace tailWord_444835 prefixEnd_444835 101517407530165473207443 := by
  unfold tailWord_444835
  simp only [CollatzResearch.WordTrace]
  refine ⟨16224465343446241614687959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10816310228964161076458639 16224465343446241614687959)
  ·
    refine ⟨24336698015169362422031939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16224465343446241614687959 24336698015169362422031939)
    ·
      refine ⟨36505047022754043633047909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24336698015169362422031939 36505047022754043633047909)
      ·
        refine ⟨6844696316766383181196483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36505047022754043633047909 6844696316766383181196483)
        ·
          refine ⟨10267044475149574771794725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6844696316766383181196483 10267044475149574771794725)
          ·
            refine ⟨1925070839090545269711511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10267044475149574771794725 1925070839090545269711511)
            ·
              refine ⟨2887606258635817904567267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1925070839090545269711511 2887606258635817904567267)
              ·
                refine ⟨4331409387953726856850901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2887606258635817904567267 4331409387953726856850901)
                ·
                  refine ⟨101517407530165473207443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4331409387953726856850901 101517407530165473207443)
                  ·
                    rfl

theorem cell21_444835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 7].length) (baseStart_444835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444835 prefixEnd_444835 := by exact prefixLift 444835
  have htrace : WordTrace (prefixWord ++ tailWord_444835) baseStart_444835 baseEnd_444835 := by
    simpa [prefixWord, tailWord_444835, baseEnd_444835] using wordTrace_append hprefix tailTrace_444835
  have hstable : (prefixWord ++ tailWord_444835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444835).length < 2 ^ (prefixWord ++ tailWord_444835).sum := by decide
  have hdescent : baseEnd_444835 < baseStart_444835 := by decide
  rcases family_descends (prefixWord ++ tailWord_444835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444914 : List Nat := [3, 2, 1, 4, 2, 2, 7]
def baseStart_444914 : Nat := 118140960795 + 444914 * 2 ^ 59
def prefixEnd_444914 : Nat := 4983230072969 + 3 ^ 40 * 444914 * 2
def baseEnd_444914 : Nat := 11281715156275432376735

theorem tailTrace_444914 : CollatzResearch.WordTrace tailWord_444914 prefixEnd_444914 11281715156275432376735 := by
  unfold tailWord_444914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4056836677540009526703449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10818231140106692071209197 4056836677540009526703449)
  ·
    refine ⟨3042627508155007145027587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4056836677540009526703449 3042627508155007145027587)
    ·
      refine ⟨4563941262232510717541381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3042627508155007145027587 4563941262232510717541381)
      ·
        refine ⟨855738986668595759539009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4563941262232510717541381 855738986668595759539009)
        ·
          refine ⟨641804240001446819654257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 855738986668595759539009 641804240001446819654257)
          ·
            refine ⟨481353180001085114740693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 641804240001446819654257 481353180001085114740693)
            ·
              refine ⟨11281715156275432376735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 481353180001085114740693 11281715156275432376735)
              ·
                rfl

theorem cell21_444914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 7].length) (baseStart_444914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444914 prefixEnd_444914 := by exact prefixLift 444914
  have htrace : WordTrace (prefixWord ++ tailWord_444914) baseStart_444914 baseEnd_444914 := by
    simpa [prefixWord, tailWord_444914, baseEnd_444914] using wordTrace_append hprefix tailTrace_444914
  have hstable : (prefixWord ++ tailWord_444914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444914).length < 2 ^ (prefixWord ++ tailWord_444914).sum := by decide
  have hdescent : baseEnd_444914 < baseStart_444914 := by decide
  rcases family_descends (prefixWord ++ tailWord_444914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444934 : List Nat := [6, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_444934 : Nat := 118140960795 + 444934 * 2 ^ 59
def prefixEnd_444934 : Nat := 4983230072969 + 3 ^ 40 * 444934 * 2
def baseEnd_444934 : Nat := 101540000678963301057241

theorem tailTrace_444934 : CollatzResearch.WordTrace tailWord_444934 prefixEnd_444934 101540000678963301057241 := by
  unfold tailWord_444934
  simp only [CollatzResearch.WordTrace]
  refine ⟨507127380315236922579433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10818717446725054348361237 507127380315236922579433)
  ·
    refine ⟨380345535236427691934575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 507127380315236922579433 380345535236427691934575)
    ·
      refine ⟨570518302854641537901863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380345535236427691934575 570518302854641537901863)
      ·
        refine ⟨855777454281962306852795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570518302854641537901863 855777454281962306852795)
        ·
          refine ⟨1283666181422943460279193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855777454281962306852795 1283666181422943460279193)
          ·
            refine ⟨962749636067207595209395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1283666181422943460279193 962749636067207595209395)
            ·
              refine ⟨1444124454100811392814093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962749636067207595209395 1444124454100811392814093)
              ·
                refine ⟨541546670287804272305285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1444124454100811392814093 541546670287804272305285)
                ·
                  refine ⟨101540000678963301057241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 541546670287804272305285 101540000678963301057241)
                  ·
                    rfl

theorem cell21_444934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_444934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_444934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_444934 prefixEnd_444934 := by exact prefixLift 444934
  have htrace : WordTrace (prefixWord ++ tailWord_444934) baseStart_444934 baseEnd_444934 := by
    simpa [prefixWord, tailWord_444934, baseEnd_444934] using wordTrace_append hprefix tailTrace_444934
  have hstable : (prefixWord ++ tailWord_444934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444934).length < 2 ^ (prefixWord ++ tailWord_444934).sum := by decide
  have hdescent : baseEnd_444934 < baseStart_444934 := by decide
  rcases family_descends (prefixWord ++ tailWord_444934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445001 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 10]
def baseStart_445001 : Nat := 118140960795 + 445001 * 2 ^ 59
def prefixEnd_445001 : Nat := 4983230072969 + 3 ^ 40 * 445001 * 2
def baseEnd_445001 : Nat := 101555290991786073440437

theorem tailTrace_445001 : CollatzResearch.WordTrace tailWord_445001 prefixEnd_445001 101555290991786073440437 := by
  unfold tailWord_445001
  simp only [CollatzResearch.WordTrace]
  refine ⟨16230519860844851965230857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10820346573896567976820571 16230519860844851965230857)
  ·
    refine ⟨12172889895633638973923143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16230519860844851965230857 12172889895633638973923143)
    ·
      refine ⟨18259334843450458460884715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12172889895633638973923143 18259334843450458460884715)
      ·
        refine ⟨27389002265175687691327073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18259334843450458460884715 27389002265175687691327073)
        ·
          refine ⟨20541751698881765768495305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27389002265175687691327073 20541751698881765768495305)
          ·
            refine ⟨15406313774161324326371479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20541751698881765768495305 15406313774161324326371479)
            ·
              refine ⟨23109470661241986489557219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15406313774161324326371479 23109470661241986489557219)
              ·
                refine ⟨34664205991862979734335829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23109470661241986489557219 34664205991862979734335829)
                ·
                  refine ⟨101555290991786073440437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 34664205991862979734335829 101555290991786073440437)
                  ·
                    rfl

theorem cell21_445001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_445001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_445001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_445001 prefixEnd_445001 := by exact prefixLift 445001
  have htrace : WordTrace (prefixWord ++ tailWord_445001) baseStart_445001 baseEnd_445001 := by
    simpa [prefixWord, tailWord_445001, baseEnd_445001] using wordTrace_append hprefix tailTrace_445001
  have hstable : (prefixWord ++ tailWord_445001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445001).length < 2 ^ (prefixWord ++ tailWord_445001).sum := by decide
  have hdescent : baseEnd_445001 < baseStart_445001 := by decide
  rcases family_descends (prefixWord ++ tailWord_445001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445058 : List Nat := [3, 4, 3, 1, 2, 1, 2, 5]
def baseStart_445058 : Nat := 118140960795 + 445058 * 2 ^ 59
def prefixEnd_445058 : Nat := 4983230072969 + 3 ^ 40 * 445058 * 2
def baseEnd_445058 : Nat := 33856099722788880330107

theorem tailTrace_445058 : CollatzResearch.WordTrace tailWord_445058 prefixEnd_445058 33856099722788880330107 := by
  unfold tailWord_445058
  simp only [CollatzResearch.WordTrace]
  refine ⟨4058149705409587675013957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10821732547758900466703885 4058149705409587675013957)
  ·
    refine ⟨760903069764297689065117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4058149705409587675013957 760903069764297689065117)
    ·
      refine ⟨285338651161611633399419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 760903069764297689065117 285338651161611633399419)
      ·
        refine ⟨428007976742417450099129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285338651161611633399419 428007976742417450099129)
        ·
          refine ⟨321005982556813087574347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428007976742417450099129 321005982556813087574347)
          ·
            refine ⟨481508973835219631361521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321005982556813087574347 481508973835219631361521)
            ·
              refine ⟨361131730376414723521141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481508973835219631361521 361131730376414723521141)
              ·
                refine ⟨33856099722788880330107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 361131730376414723521141 33856099722788880330107)
                ·
                  rfl

theorem cell21_445058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_445058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_445058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_445058 prefixEnd_445058 := by exact prefixLift 445058
  have htrace : WordTrace (prefixWord ++ tailWord_445058) baseStart_445058 baseEnd_445058 := by
    simpa [prefixWord, tailWord_445058, baseEnd_445058] using wordTrace_append hprefix tailTrace_445058
  have hstable : (prefixWord ++ tailWord_445058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445058).length < 2 ^ (prefixWord ++ tailWord_445058).sum := by decide
  have hdescent : baseEnd_445058 < baseStart_445058 := by decide
  rcases family_descends (prefixWord ++ tailWord_445058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445063 : List Nat := [1, 1, 4, 2, 1, 2, 1, 4, 5]
def baseStart_445063 : Nat := 118140960795 + 445063 * 2 ^ 59
def prefixEnd_445063 : Nat := 4983230072969 + 3 ^ 40 * 445063 * 2
def baseEnd_445063 : Nat := 101569440236487743406977

theorem tailTrace_445063 : CollatzResearch.WordTrace tailWord_445063 prefixEnd_445063 101569440236487743406977 := by
  unfold tailWord_445063
  simp only [CollatzResearch.WordTrace]
  refine ⟨16232781186620236553987843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10821854124413491035991895 16232781186620236553987843)
  ·
    refine ⟨24349171779930354830981765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16232781186620236553987843 24349171779930354830981765)
    ·
      refine ⟨4565469708736941530809081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24349171779930354830981765 4565469708736941530809081)
      ·
        refine ⟨3424102281552706148106811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4565469708736941530809081 3424102281552706148106811)
        ·
          refine ⟨5136153422329059222160217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3424102281552706148106811 5136153422329059222160217)
          ·
            refine ⟨3852115066746794416620163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5136153422329059222160217 3852115066746794416620163)
            ·
              refine ⟨5778172600120191624930245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3852115066746794416620163 5778172600120191624930245)
              ·
                refine ⟨1083407362522535929674421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5778172600120191624930245 1083407362522535929674421)
                ·
                  refine ⟨101569440236487743406977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1083407362522535929674421 101569440236487743406977)
                  ·
                    rfl

theorem cell21_445063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 5].length) (baseStart_445063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_445063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_445063 prefixEnd_445063 := by exact prefixLift 445063
  have htrace : WordTrace (prefixWord ++ tailWord_445063) baseStart_445063 baseEnd_445063 := by
    simpa [prefixWord, tailWord_445063, baseEnd_445063] using wordTrace_append hprefix tailTrace_445063
  have hstable : (prefixWord ++ tailWord_445063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445063).length < 2 ^ (prefixWord ++ tailWord_445063).sum := by decide
  have hdescent : baseEnd_445063 < baseStart_445063 := by decide
  rcases family_descends (prefixWord ++ tailWord_445063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445111 : List Nat := [1, 1, 3, 1, 6, 1, 1, 3, 4]
def baseStart_445111 : Nat := 118140960795 + 445111 * 2 ^ 59
def prefixEnd_445111 : Nat := 4983230072969 + 3 ^ 40 * 445111 * 2
def baseEnd_445111 : Nat := 101580394490450326606879

theorem tailTrace_445111 : CollatzResearch.WordTrace tailWord_445111 prefixEnd_445111 101580394490450326606879 := by
  unfold tailWord_445111
  simp only [CollatzResearch.WordTrace]
  refine ⟨16234531890446340751735187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10823021260297560501156791 16234531890446340751735187)
  ·
    refine ⟨24351797835669511127602781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16234531890446340751735187 24351797835669511127602781)
    ·
      refine ⟨9131924188376066672851043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24351797835669511127602781 9131924188376066672851043)
      ·
        refine ⟨13697886282564100009276565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9131924188376066672851043 13697886282564100009276565)
        ·
          refine ⟨642088419495192187934839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13697886282564100009276565 642088419495192187934839)
          ·
            refine ⟨963132629242788281902259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642088419495192187934839 963132629242788281902259)
            ·
              refine ⟨1444698943864182422853389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963132629242788281902259 1444698943864182422853389)
              ·
                refine ⟨541762103949068408570021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1444698943864182422853389 541762103949068408570021)
                ·
                  refine ⟨101580394490450326606879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 541762103949068408570021 101580394490450326606879)
                  ·
                    rfl

theorem cell21_445111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 4].length) (baseStart_445111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_445111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_445111 prefixEnd_445111 := by exact prefixLift 445111
  have htrace : WordTrace (prefixWord ++ tailWord_445111) baseStart_445111 baseEnd_445111 := by
    simpa [prefixWord, tailWord_445111, baseEnd_445111] using wordTrace_append hprefix tailTrace_445111
  have hstable : (prefixWord ++ tailWord_445111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445111).length < 2 ^ (prefixWord ++ tailWord_445111).sum := by decide
  have hdescent : baseEnd_445111 < baseStart_445111 := by decide
  rcases family_descends (prefixWord ++ tailWord_445111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445215 : List Nat := [1, 1, 2, 4, 2, 2, 1, 3, 5]
def baseStart_445215 : Nat := 118140960795 + 445215 * 2 ^ 59
def prefixEnd_445215 : Nat := 4983230072969 + 3 ^ 40 * 445215 * 2
def baseEnd_445215 : Nat := 101604128707369256873333

theorem tailTrace_445215 : CollatzResearch.WordTrace tailWord_445215 prefixEnd_445215 101604128707369256873333 := by
  unfold tailWord_445215
  simp only [CollatzResearch.WordTrace]
  refine ⟨16238325082069566513521099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10825550054713044342347399 16238325082069566513521099)
  ·
    refine ⟨24357487623104349770281649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16238325082069566513521099 24357487623104349770281649)
    ·
      refine ⟨18268115717328262327711237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24357487623104349770281649 18268115717328262327711237)
      ·
        refine ⟨3425271696999049186445857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18268115717328262327711237 3425271696999049186445857)
        ·
          refine ⟨2568953772749286889834393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3425271696999049186445857 2568953772749286889834393)
          ·
            refine ⟨1926715329561965167375795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2568953772749286889834393 1926715329561965167375795)
            ·
              refine ⟨2890072994342947751063693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1926715329561965167375795 2890072994342947751063693)
              ·
                refine ⟨1083777372878605406648885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2890072994342947751063693 1083777372878605406648885)
                ·
                  refine ⟨101604128707369256873333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1083777372878605406648885 101604128707369256873333)
                  ·
                    rfl

theorem cell21_445215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 5].length) (baseStart_445215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_445215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_445215 prefixEnd_445215 := by exact prefixLift 445215
  have htrace : WordTrace (prefixWord ++ tailWord_445215) baseStart_445215 baseEnd_445215 := by
    simpa [prefixWord, tailWord_445215, baseEnd_445215] using wordTrace_append hprefix tailTrace_445215
  have hstable : (prefixWord ++ tailWord_445215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445215).length < 2 ^ (prefixWord ++ tailWord_445215).sum := by decide
  have hdescent : baseEnd_445215 < baseStart_445215 := by decide
  rcases family_descends (prefixWord ++ tailWord_445215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445260 : List Nat := [2, 2, 1, 3, 3, 1, 9]
def baseStart_445260 : Nat := 118140960795 + 445260 * 2 ^ 59
def prefixEnd_445260 : Nat := 4983230072969 + 3 ^ 40 * 445260 * 2
def baseEnd_445260 : Nat := 11290488702273242069249

theorem tailTrace_445260 : CollatzResearch.WordTrace tailWord_445260 prefixEnd_445260 11290488702273242069249 := by
  unfold tailWord_445260
  simp only [CollatzResearch.WordTrace]
  refine ⟨8119983183453269599454617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10826644244604359465939489 8119983183453269599454617)
  ·
    refine ⟨6089987387589952199590963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8119983183453269599454617 6089987387589952199590963)
    ·
      refine ⟨9134981081384928299386445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6089987387589952199590963 9134981081384928299386445)
      ·
        refine ⟨3425617905519348112269917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9134981081384928299386445 3425617905519348112269917)
        ·
          refine ⟨1284606714569755542101219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3425617905519348112269917 1284606714569755542101219)
          ·
            refine ⟨1926910071854633313151829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284606714569755542101219 1926910071854633313151829)
            ·
              refine ⟨11290488702273242069249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1926910071854633313151829 11290488702273242069249)
              ·
                rfl

theorem cell21_445260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 9].length) (baseStart_445260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_445260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_445260 prefixEnd_445260 := by exact prefixLift 445260
  have htrace : WordTrace (prefixWord ++ tailWord_445260) baseStart_445260 baseEnd_445260 := by
    simpa [prefixWord, tailWord_445260, baseEnd_445260] using wordTrace_append hprefix tailTrace_445260
  have hstable : (prefixWord ++ tailWord_445260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445260).length < 2 ^ (prefixWord ++ tailWord_445260).sum := by decide
  have hdescent : baseEnd_445260 < baseStart_445260 := by decide
  rcases family_descends (prefixWord ++ tailWord_445260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445384 : List Nat := [2, 1, 3, 1, 5, 1, 2, 1, 5]
def baseStart_445384 : Nat := 118140960795 + 445384 * 2 ^ 59
def prefixEnd_445384 : Nat := 4983230072969 + 3 ^ 40 * 445384 * 2
def baseEnd_445384 : Nat := 101642696809862518556321

theorem tailTrace_445384 : CollatzResearch.WordTrace tailWord_445384 prefixEnd_445384 101642696809862518556321 := by
  unfold tailWord_445384
  simp only [CollatzResearch.WordTrace]
  refine ⟨8122244509228654188211603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10829659345638205584282137 8122244509228654188211603)
  ·
    refine ⟨12183366763842981282317405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8122244509228654188211603 12183366763842981282317405)
    ·
      refine ⟨4568762536441117980869027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12183366763842981282317405 4568762536441117980869027)
      ·
        refine ⟨6853143804661676971303541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4568762536441117980869027 6853143804661676971303541)
        ·
          refine ⟨642482231687032216059707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6853143804661676971303541 642482231687032216059707)
          ·
            refine ⟨963723347530548324089561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642482231687032216059707 963723347530548324089561)
            ·
              refine ⟨722792510647911243067171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 963723347530548324089561 722792510647911243067171)
              ·
                refine ⟨1084188765971866864600757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722792510647911243067171 1084188765971866864600757)
                ·
                  refine ⟨101642696809862518556321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1084188765971866864600757 101642696809862518556321)
                  ·
                    rfl

theorem cell21_445384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_445384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_445384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_445384 prefixEnd_445384 := by exact prefixLift 445384
  have htrace : WordTrace (prefixWord ++ tailWord_445384) baseStart_445384 baseEnd_445384 := by
    simpa [prefixWord, tailWord_445384, baseEnd_445384] using wordTrace_append hprefix tailTrace_445384
  have hstable : (prefixWord ++ tailWord_445384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445384).length < 2 ^ (prefixWord ++ tailWord_445384).sum := by decide
  have hdescent : baseEnd_445384 < baseStart_445384 := by decide
  rcases family_descends (prefixWord ++ tailWord_445384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445494 : List Nat := [5, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_445494 : Nat := 118140960795 + 445494 * 2 ^ 59
def prefixEnd_445494 : Nat := 4983230072969 + 3 ^ 40 * 445494 * 2
def baseEnd_445494 : Nat := 101667800308526771722763

theorem tailTrace_445494 : CollatzResearch.WordTrace tailWord_445494 prefixEnd_445494 101667800308526771722763 := by
  unfold tailWord_445494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1015531315503674822682971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10832334032039198108618357 1015531315503674822682971)
  ·
    refine ⟨1523296973255512234024457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1015531315503674822682971 1523296973255512234024457)
    ·
      refine ⟨1142472729941634175518343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1523296973255512234024457 1142472729941634175518343)
      ·
        refine ⟨1713709094912451263277515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1142472729941634175518343 1713709094912451263277515)
        ·
          refine ⟨2570563642368676894916273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1713709094912451263277515 2570563642368676894916273)
          ·
            refine ⟨1927922731776507671187205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2570563642368676894916273 1927922731776507671187205)
            ·
              refine ⟨361485512208095188347601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1927922731776507671187205 361485512208095188347601)
              ·
                refine ⟨271114134156071391260701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361485512208095188347601 271114134156071391260701)
                ·
                  refine ⟨101667800308526771722763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271114134156071391260701 101667800308526771722763)
                  ·
                    rfl

theorem cell21_445494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_445494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_445494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_445494 prefixEnd_445494 := by exact prefixLift 445494
  have htrace : WordTrace (prefixWord ++ tailWord_445494) baseStart_445494 baseEnd_445494 := by
    simpa [prefixWord, tailWord_445494, baseEnd_445494] using wordTrace_append hprefix tailTrace_445494
  have hstable : (prefixWord ++ tailWord_445494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445494).length < 2 ^ (prefixWord ++ tailWord_445494).sum := by decide
  have hdescent : baseEnd_445494 < baseStart_445494 := by decide
  rcases family_descends (prefixWord ++ tailWord_445494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445536 : List Nat := [2, 1, 1, 3, 2, 2, 4, 3, 3]
def baseStart_445536 : Nat := 118140960795 + 445536 * 2 ^ 59
def prefixEnd_445536 : Nat := 4983230072969 + 3 ^ 40 * 445536 * 2
def baseEnd_445536 : Nat := 101677385280744032022677

theorem tailTrace_445536 : CollatzResearch.WordTrace tailWord_445536 prefixEnd_445536 101677385280744032022677 := by
  unfold tailWord_445536
  simp only [CollatzResearch.WordTrace]
  refine ⟨8125016456953319167978231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10833355275937758890637641 8125016456953319167978231)
  ·
    refine ⟨12187524685429978751967347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8125016456953319167978231 12187524685429978751967347)
    ·
      refine ⟨18281287028144968127951021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12187524685429978751967347 18281287028144968127951021)
      ·
        refine ⟨6855482635554363047981633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18281287028144968127951021 6855482635554363047981633)
        ·
          refine ⟨5141611976665772285986225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6855482635554363047981633 5141611976665772285986225)
          ·
            refine ⟨3856208982499329214489669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5141611976665772285986225 3856208982499329214489669)
            ·
              refine ⟨723039184218624227716813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3856208982499329214489669 723039184218624227716813)
              ·
                refine ⟨271139694081984085393805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 723039184218624227716813 271139694081984085393805)
                ·
                  refine ⟨101677385280744032022677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271139694081984085393805 101677385280744032022677)
                  ·
                    rfl

theorem cell21_445536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 3].length) (baseStart_445536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_445536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_445536 prefixEnd_445536 := by exact prefixLift 445536
  have htrace : WordTrace (prefixWord ++ tailWord_445536) baseStart_445536 baseEnd_445536 := by
    simpa [prefixWord, tailWord_445536, baseEnd_445536] using wordTrace_append hprefix tailTrace_445536
  have hstable : (prefixWord ++ tailWord_445536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445536).length < 2 ^ (prefixWord ++ tailWord_445536).sum := by decide
  have hdescent : baseEnd_445536 < baseStart_445536 := by decide
  rcases family_descends (prefixWord ++ tailWord_445536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445550 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_445550 : Nat := 118140960795 + 445550 * 2 ^ 59
def prefixEnd_445550 : Nat := 4983230072969 + 3 ^ 40 * 445550 * 2
def baseEnd_445550 : Nat := 101680580271483118789315

theorem tailTrace_445550 : CollatzResearch.WordTrace tailWord_445550 prefixEnd_445550 101680580271483118789315 := by
  unfold tailWord_445550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2031317941981989840870763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10833695690570612484644069 2031317941981989840870763)
  ·
    refine ⟨3046976912972984761306145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2031317941981989840870763 3046976912972984761306145)
    ·
      refine ⟨2285232684729738570979609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3046976912972984761306145 2285232684729738570979609)
      ·
        refine ⟨1713924513547303928234707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2285232684729738570979609 1713924513547303928234707)
        ·
          refine ⟨2570886770320955892352061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1713924513547303928234707 2570886770320955892352061)
          ·
            refine ⟨964082538870358459632023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2570886770320955892352061 964082538870358459632023)
            ·
              refine ⟨1446123808305537689448035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964082538870358459632023 1446123808305537689448035)
              ·
                refine ⟨2169185712458306534172053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446123808305537689448035 2169185712458306534172053)
                ·
                  refine ⟨101680580271483118789315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2169185712458306534172053 101680580271483118789315)
                  ·
                    rfl

theorem cell21_445550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_445550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_445550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_445550 prefixEnd_445550 := by exact prefixLift 445550
  have htrace : WordTrace (prefixWord ++ tailWord_445550) baseStart_445550 baseEnd_445550 := by
    simpa [prefixWord, tailWord_445550, baseEnd_445550] using wordTrace_append hprefix tailTrace_445550
  have hstable : (prefixWord ++ tailWord_445550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445550).length < 2 ^ (prefixWord ++ tailWord_445550).sum := by decide
  have hdescent : baseEnd_445550 < baseStart_445550 := by decide
  rcases family_descends (prefixWord ++ tailWord_445550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445750 : List Nat := [5, 1, 2, 3, 1, 1, 1, 7]
def baseStart_445750 : Nat := 118140960795 + 445750 * 2 ^ 59
def prefixEnd_445750 : Nat := 4983230072969 + 3 ^ 40 * 445750 * 2
def baseEnd_445750 : Nat := 33908740998775738485191

theorem tailTrace_445750 : CollatzResearch.WordTrace tailWord_445750 prefixEnd_445750 33908740998775738485191 := by
  unfold tailWord_445750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016114883445709555265419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10838558756754235256164469 1016114883445709555265419)
  ·
    refine ⟨1524172325168564332898129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1016114883445709555265419 1524172325168564332898129)
    ·
      refine ⟨1143129243876423249673597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1524172325168564332898129 1143129243876423249673597)
      ·
        refine ⟨428673466453658718627599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1143129243876423249673597 428673466453658718627599)
        ·
          refine ⟨643010199680488077941399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428673466453658718627599 643010199680488077941399)
          ·
            refine ⟨964515299520732116912099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643010199680488077941399 964515299520732116912099)
            ·
              refine ⟨1446772949281098175368149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964515299520732116912099 1446772949281098175368149)
              ·
                refine ⟨33908740998775738485191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1446772949281098175368149 33908740998775738485191)
                ·
                  rfl

theorem cell21_445750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_445750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_445750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_445750 prefixEnd_445750 := by exact prefixLift 445750
  have htrace : WordTrace (prefixWord ++ tailWord_445750) baseStart_445750 baseEnd_445750 := by
    simpa [prefixWord, tailWord_445750, baseEnd_445750] using wordTrace_append hprefix tailTrace_445750
  have hstable : (prefixWord ++ tailWord_445750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445750).length < 2 ^ (prefixWord ++ tailWord_445750).sum := by decide
  have hdescent : baseEnd_445750 < baseStart_445750 := by decide
  rcases family_descends (prefixWord ++ tailWord_445750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445781 : List Nat := [1, 3, 2, 2, 3, 2, 3, 2, 3]
def baseStart_445781 : Nat := 118140960795 + 445781 * 2 ^ 59
def prefixEnd_445781 : Nat := 4983230072969 + 3 ^ 40 * 445781 * 2
def baseEnd_445781 : Nat := 101733297618678050438843

theorem tailTrace_445781 : CollatzResearch.WordTrace tailWord_445781 prefixEnd_445781 101733297618678050438843 := by
  unfold tailWord_445781
  simp only [CollatzResearch.WordTrace]
  refine ⟨16258968798019045178625197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10839312532012696785750131 16258968798019045178625197)
  ·
    refine ⟨6097113299257141941984449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16258968798019045178625197 6097113299257141941984449)
    ·
      refine ⟨4572834974442856456488337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6097113299257141941984449 4572834974442856456488337)
      ·
        refine ⟨3429626230832142342366253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4572834974442856456488337 3429626230832142342366253)
        ·
          refine ⟨1286109836562053378387345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3429626230832142342366253 1286109836562053378387345)
          ·
            refine ⟨964582377421540033790509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1286109836562053378387345 964582377421540033790509)
            ·
              refine ⟨361718391533077512671441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 964582377421540033790509 361718391533077512671441)
              ·
                refine ⟨271288793649808134503581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361718391533077512671441 271288793649808134503581)
                ·
                  refine ⟨101733297618678050438843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271288793649808134503581 101733297618678050438843)
                  ·
                    rfl

theorem cell21_445781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_445781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_445781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_445781 prefixEnd_445781 := by exact prefixLift 445781
  have htrace : WordTrace (prefixWord ++ tailWord_445781) baseStart_445781 baseEnd_445781 := by
    simpa [prefixWord, tailWord_445781, baseEnd_445781] using wordTrace_append hprefix tailTrace_445781
  have hstable : (prefixWord ++ tailWord_445781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445781).length < 2 ^ (prefixWord ++ tailWord_445781).sum := by decide
  have hdescent : baseEnd_445781 < baseStart_445781 := by decide
  rcases family_descends (prefixWord ++ tailWord_445781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445792 : List Nat := [2, 1, 1, 3, 4, 2, 2, 6]
def baseStart_445792 : Nat := 118140960795 + 445792 * 2 ^ 59
def prefixEnd_445792 : Nat := 4983230072969 + 3 ^ 40 * 445792 * 2
def baseEnd_445792 : Nat := 33911935989514825251829

theorem tailTrace_445792 : CollatzResearch.WordTrace tailWord_445792 prefixEnd_445792 33911935989514825251829 := by
  unfold tailWord_445792
  simp only [CollatzResearch.WordTrace]
  refine ⟨8129685000489597028637815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10839580000652796038183753 8129685000489597028637815)
  ·
    refine ⟨12194527500734395542956723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8129685000489597028637815 12194527500734395542956723)
    ·
      refine ⟨18291791251101593314435085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12194527500734395542956723 18291791251101593314435085)
      ·
        refine ⟨6859421719163097492913157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18291791251101593314435085 6859421719163097492913157)
        ·
          refine ⟨1286141572343080779921217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6859421719163097492913157 1286141572343080779921217)
          ·
            refine ⟨964606179257310584940913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1286141572343080779921217 964606179257310584940913)
            ·
              refine ⟨723454634442982938705685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 964606179257310584940913 723454634442982938705685)
              ·
                refine ⟨33911935989514825251829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 723454634442982938705685 33911935989514825251829)
                ·
                  rfl

theorem cell21_445792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 6].length) (baseStart_445792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_445792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_445792 prefixEnd_445792 := by exact prefixLift 445792
  have htrace : WordTrace (prefixWord ++ tailWord_445792) baseStart_445792 baseEnd_445792 := by
    simpa [prefixWord, tailWord_445792, baseEnd_445792] using wordTrace_append hprefix tailTrace_445792
  have hstable : (prefixWord ++ tailWord_445792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445792).length < 2 ^ (prefixWord ++ tailWord_445792).sum := by decide
  have hdescent : baseEnd_445792 < baseStart_445792 := by decide
  rcases family_descends (prefixWord ++ tailWord_445792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445795 : List Nat := [1, 1, 1, 5, 2, 4, 2, 1, 4]
def baseStart_445795 : Nat := 118140960795 + 445795 * 2 ^ 59
def prefixEnd_445795 : Nat := 4983230072969 + 3 ^ 40 * 445795 * 2
def baseEnd_445795 : Nat := 101736492609417137205481

theorem tailTrace_445795 : CollatzResearch.WordTrace tailWord_445795 prefixEnd_445795 101736492609417137205481 := by
  unfold tailWord_445795
  simp only [CollatzResearch.WordTrace]
  refine ⟨16259479419968325569634839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10839652946645550379756559 16259479419968325569634839)
  ·
    refine ⟨24389219129952488354452259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16259479419968325569634839 24389219129952488354452259)
    ·
      refine ⟨36583828694928732531678389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24389219129952488354452259 36583828694928732531678389)
      ·
        refine ⟨3429733940149568674844849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36583828694928732531678389 3429733940149568674844849)
        ·
          refine ⟨2572300455112176506133637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3429733940149568674844849 2572300455112176506133637)
          ·
            refine ⟨482306335333533094900057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2572300455112176506133637 482306335333533094900057)
            ·
              refine ⟨361729751500149821175043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482306335333533094900057 361729751500149821175043)
              ·
                refine ⟨542594627250224731762565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361729751500149821175043 542594627250224731762565)
                ·
                  refine ⟨101736492609417137205481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 542594627250224731762565 101736492609417137205481)
                  ·
                    rfl

theorem cell21_445795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 4].length) (baseStart_445795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_445795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_445795 prefixEnd_445795 := by exact prefixLift 445795
  have htrace : WordTrace (prefixWord ++ tailWord_445795) baseStart_445795 baseEnd_445795 := by
    simpa [prefixWord, tailWord_445795, baseEnd_445795] using wordTrace_append hprefix tailTrace_445795
  have hstable : (prefixWord ++ tailWord_445795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445795).length < 2 ^ (prefixWord ++ tailWord_445795).sum := by decide
  have hdescent : baseEnd_445795 < baseStart_445795 := by decide
  rcases family_descends (prefixWord ++ tailWord_445795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445899 : List Nat := [1, 1, 1, 1, 3, 3, 4, 4, 3]
def baseStart_445899 : Nat := 118140960795 + 445899 * 2 ^ 59
def prefixEnd_445899 : Nat := 4983230072969 + 3 ^ 40 * 445899 * 2
def baseEnd_445899 : Nat := 101760226826336067471935

theorem tailTrace_445899 : CollatzResearch.WordTrace tailWord_445899 prefixEnd_445899 101760226826336067471935 := by
  unfold tailWord_445899
  simp only [CollatzResearch.WordTrace]
  refine ⟨16263272611591551331420751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10842181741061034220947167 16263272611591551331420751)
  ·
    refine ⟨24394908917387326997131127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16263272611591551331420751 24394908917387326997131127)
    ·
      refine ⟨36592363376080990495696691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24394908917387326997131127 36592363376080990495696691)
      ·
        refine ⟨54888545064121485743545037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36592363376080990495696691 54888545064121485743545037)
        ·
          refine ⟨20583204399045557153829389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54888545064121485743545037 20583204399045557153829389)
          ·
            refine ⟨7718701649642083932686021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20583204399045557153829389 7718701649642083932686021)
            ·
              refine ⟨1447256559307890737378629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7718701649642083932686021 1447256559307890737378629)
              ·
                refine ⟨271360604870229513258493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1447256559307890737378629 271360604870229513258493)
                ·
                  refine ⟨101760226826336067471935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271360604870229513258493 101760226826336067471935)
                  ·
                    rfl

theorem cell21_445899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 3].length) (baseStart_445899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_445899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_445899 prefixEnd_445899 := by exact prefixLift 445899
  have htrace : WordTrace (prefixWord ++ tailWord_445899) baseStart_445899 baseEnd_445899 := by
    simpa [prefixWord, tailWord_445899, baseEnd_445899] using wordTrace_append hprefix tailTrace_445899
  have hstable : (prefixWord ++ tailWord_445899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445899).length < 2 ^ (prefixWord ++ tailWord_445899).sum := by decide
  have hdescent : baseEnd_445899 < baseStart_445899 := by decide
  rcases family_descends (prefixWord ++ tailWord_445899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445950 : List Nat := [4, 2, 2, 3, 2, 1, 1, 1, 5]
def baseStart_445950 : Nat := 118140960795 + 445950 * 2 ^ 59
def prefixEnd_445950 : Nat := 4983230072969 + 3 ^ 40 * 445950 * 2
def baseEnd_445950 : Nat := 101771865721171312121831

theorem tailTrace_445950 : CollatzResearch.WordTrace tailWord_445950 prefixEnd_445950 101771865721171312121831 := by
  unfold tailWord_445950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2033141591800848380190913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10843421822937858027684869 2033141591800848380190913)
  ·
    refine ⟨1524856193850636285143185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2033141591800848380190913 1524856193850636285143185)
    ·
      refine ⟨1143642145387977213857389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1524856193850636285143185 1143642145387977213857389)
      ·
        refine ⟨428865804520491455196521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1143642145387977213857389 428865804520491455196521)
        ·
          refine ⟨321649353390368591397391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428865804520491455196521 321649353390368591397391)
          ·
            refine ⟨482474030085552887096087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321649353390368591397391 482474030085552887096087)
            ·
              refine ⟨723711045128329330644131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482474030085552887096087 723711045128329330644131)
              ·
                refine ⟨1085566567692493995966197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723711045128329330644131 1085566567692493995966197)
                ·
                  refine ⟨101771865721171312121831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1085566567692493995966197 101771865721171312121831)
                  ·
                    rfl

theorem cell21_445950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_445950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_445950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_445950 prefixEnd_445950 := by exact prefixLift 445950
  have htrace : WordTrace (prefixWord ++ tailWord_445950) baseStart_445950 baseEnd_445950 := by
    simpa [prefixWord, tailWord_445950, baseEnd_445950] using wordTrace_append hprefix tailTrace_445950
  have hstable : (prefixWord ++ tailWord_445950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445950).length < 2 ^ (prefixWord ++ tailWord_445950).sum := by decide
  have hdescent : baseEnd_445950 < baseStart_445950 := by decide
  rcases family_descends (prefixWord ++ tailWord_445950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445964 : List Nat := [2, 2, 1, 2, 6, 1, 2, 1, 4]
def baseStart_445964 : Nat := 118140960795 + 445964 * 2 ^ 59
def prefixEnd_445964 : Nat := 4983230072969 + 3 ^ 40 * 445964 * 2
def baseEnd_445964 : Nat := 101775060711910398888469

theorem tailTrace_445964 : CollatzResearch.WordTrace tailWord_445964 prefixEnd_445964 101775060711910398888469 := by
  unfold tailWord_445964
  simp only [CollatzResearch.WordTrace]
  refine ⟨8132821678178033716268473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10843762237570711621691297 8132821678178033716268473)
  ·
    refine ⟨6099616258633525287201355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8132821678178033716268473 6099616258633525287201355)
    ·
      refine ⟨9149424387950287930802033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6099616258633525287201355 9149424387950287930802033)
      ·
        refine ⟨6862068290962715948101525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9149424387950287930802033 6862068290962715948101525)
        ·
          refine ⟨321659451138877310067259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6862068290962715948101525 321659451138877310067259)
          ·
            refine ⟨482489176708315965100889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321659451138877310067259 482489176708315965100889)
            ·
              refine ⟨361866882531236973825667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482489176708315965100889 361866882531236973825667)
              ·
                refine ⟨542800323796855460738501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361866882531236973825667 542800323796855460738501)
                ·
                  refine ⟨101775060711910398888469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 542800323796855460738501 101775060711910398888469)
                  ·
                    rfl

theorem cell21_445964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_445964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_445964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_445964 prefixEnd_445964 := by exact prefixLift 445964
  have htrace : WordTrace (prefixWord ++ tailWord_445964) baseStart_445964 baseEnd_445964 := by
    simpa [prefixWord, tailWord_445964, baseEnd_445964] using wordTrace_append hprefix tailTrace_445964
  have hstable : (prefixWord ++ tailWord_445964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445964).length < 2 ^ (prefixWord ++ tailWord_445964).sum := by decide
  have hdescent : baseEnd_445964 < baseStart_445964 := by decide
  rcases family_descends (prefixWord ++ tailWord_445964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446009 : List Nat := [1, 2, 1, 5, 1, 4, 2, 2, 3]
def baseStart_446009 : Nat := 118140960795 + 446009 * 2 ^ 59
def prefixEnd_446009 : Nat := 4983230072969 + 3 ^ 40 * 446009 * 2
def baseEnd_446009 : Nat := 101785330325000320638377

theorem tailTrace_446009 : CollatzResearch.WordTrace tailWord_446009 prefixEnd_446009 101785330325000320638377 := by
  unfold tailWord_446009
  simp only [CollatzResearch.WordTrace]
  refine ⟨16267284641193040117925081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10844856427462026745283387 16267284641193040117925081)
  ·
    refine ⟨12200463480894780088443811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16267284641193040117925081 12200463480894780088443811)
    ·
      refine ⟨18300695221342170132665717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12200463480894780088443811 18300695221342170132665717)
      ·
        refine ⟨1715690177000828449937411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18300695221342170132665717 1715690177000828449937411)
        ·
          refine ⟨2573535265501242674906117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1715690177000828449937411 2573535265501242674906117)
          ·
            refine ⟨482537862281483001544897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2573535265501242674906117 482537862281483001544897)
            ·
              refine ⟨361903396711112251158673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482537862281483001544897 361903396711112251158673)
              ·
                refine ⟨271427547533334188369005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361903396711112251158673 271427547533334188369005)
                ·
                  refine ⟨101785330325000320638377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271427547533334188369005 101785330325000320638377)
                  ·
                    rfl

theorem cell21_446009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 3].length) (baseStart_446009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446009 prefixEnd_446009 := by exact prefixLift 446009
  have htrace : WordTrace (prefixWord ++ tailWord_446009) baseStart_446009 baseEnd_446009 := by
    simpa [prefixWord, tailWord_446009, baseEnd_446009] using wordTrace_append hprefix tailTrace_446009
  have hstable : (prefixWord ++ tailWord_446009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446009).length < 2 ^ (prefixWord ++ tailWord_446009).sum := by decide
  have hdescent : baseEnd_446009 < baseStart_446009 := by decide
  rcases family_descends (prefixWord ++ tailWord_446009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446034 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 7]
def baseStart_446034 : Nat := 118140960795 + 446034 * 2 ^ 59
def prefixEnd_446034 : Nat := 4983230072969 + 3 ^ 40 * 446034 * 2
def baseEnd_446034 : Nat := 101791035665605832721659

theorem tailTrace_446034 : CollatzResearch.WordTrace tailWord_446034 prefixEnd_446034 101791035665605832721659 := by
  unfold tailWord_446034
  simp only [CollatzResearch.WordTrace]
  refine ⟨4067049116525617346896289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10845464310734979591723437 4067049116525617346896289)
  ·
    refine ⟨3050286837394213010172217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4067049116525617346896289 3050286837394213010172217)
    ·
      refine ⟨2287715128045659757629163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3050286837394213010172217 2287715128045659757629163)
      ·
        refine ⟨3431572692068489636443745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2287715128045659757629163 3431572692068489636443745)
        ·
          refine ⟨2573679519051367227332809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3431572692068489636443745 2573679519051367227332809)
          ·
            refine ⟨1930259639288525420499607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2573679519051367227332809 1930259639288525420499607)
            ·
              refine ⟨2895389458932788130749411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1930259639288525420499607 2895389458932788130749411)
              ·
                refine ⟨4343084188399182196124117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2895389458932788130749411 4343084188399182196124117)
                ·
                  refine ⟨101791035665605832721659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4343084188399182196124117 101791035665605832721659)
                  ·
                    rfl

theorem cell21_446034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_446034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446034 prefixEnd_446034 := by exact prefixLift 446034
  have htrace : WordTrace (prefixWord ++ tailWord_446034) baseStart_446034 baseEnd_446034 := by
    simpa [prefixWord, tailWord_446034, baseEnd_446034] using wordTrace_append hprefix tailTrace_446034
  have hstable : (prefixWord ++ tailWord_446034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446034).length < 2 ^ (prefixWord ++ tailWord_446034).sum := by decide
  have hdescent : baseEnd_446034 < baseStart_446034 := by decide
  rcases family_descends (prefixWord ++ tailWord_446034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446048 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 6]
def baseStart_446048 : Nat := 118140960795 + 446048 * 2 ^ 59
def prefixEnd_446048 : Nat := 4983230072969 + 3 ^ 40 * 446048 * 2
def baseEnd_446048 : Nat := 101794230656344919488297

theorem tailTrace_446048 : CollatzResearch.WordTrace tailWord_446048 prefixEnd_446048 101794230656344919488297 := by
  unfold tailWord_446048
  simp only [CollatzResearch.WordTrace]
  refine ⟨8134353544025874889297399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10845804725367833185729865 8134353544025874889297399)
  ·
    refine ⟨12201530316038812333946099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8134353544025874889297399 12201530316038812333946099)
    ·
      refine ⟨18302295474058218500919149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12201530316038812333946099 18302295474058218500919149)
      ·
        refine ⟨6863360802771831937844681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18302295474058218500919149 6863360802771831937844681)
        ·
          refine ⟨5147520602078873953383511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6863360802771831937844681 5147520602078873953383511)
          ·
            refine ⟨7721280903118310930075267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5147520602078873953383511 7721280903118310930075267)
            ·
              refine ⟨11581921354677466395112901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7721280903118310930075267 11581921354677466395112901)
              ·
                refine ⟨2171610254002024949083669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11581921354677466395112901 2171610254002024949083669)
                ·
                  refine ⟨101794230656344919488297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2171610254002024949083669 101794230656344919488297)
                  ·
                    rfl

theorem cell21_446048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_446048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446048 prefixEnd_446048 := by exact prefixLift 446048
  have htrace : WordTrace (prefixWord ++ tailWord_446048) baseStart_446048 baseEnd_446048 := by
    simpa [prefixWord, tailWord_446048, baseEnd_446048] using wordTrace_append hprefix tailTrace_446048
  have hstable : (prefixWord ++ tailWord_446048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446048).length < 2 ^ (prefixWord ++ tailWord_446048).sum := by decide
  have hdescent : baseEnd_446048 < baseStart_446048 := by decide
  rcases family_descends (prefixWord ++ tailWord_446048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446051 : List Nat := [1, 1, 1, 5, 1, 3, 1, 5, 3]
def baseStart_446051 : Nat := 118140960795 + 446051 * 2 ^ 59
def prefixEnd_446051 : Nat := 4983230072969 + 3 ^ 40 * 446051 * 2
def baseEnd_446051 : Nat := 101794915297217580938291

theorem tailTrace_446051 : CollatzResearch.WordTrace tailWord_446051 prefixEnd_446051 101794915297217580938291 := by
  unfold tailWord_446051
  simp only [CollatzResearch.WordTrace]
  refine ⟨16268816507040881290954007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10845877671360587527302671 16268816507040881290954007)
  ·
    refine ⟨24403224760561321936431011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16268816507040881290954007 24403224760561321936431011)
    ·
      refine ⟨36604837140841982904646517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24403224760561321936431011 36604837140841982904646517)
      ·
        refine ⟨3431703481953935897310611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36604837140841982904646517 3431703481953935897310611)
        ·
          refine ⟨5147555222930903845965917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3431703481953935897310611 5147555222930903845965917)
          ·
            refine ⟨1930333208599088942237219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5147555222930903845965917 1930333208599088942237219)
            ·
              refine ⟨2895499812898633413355829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1930333208599088942237219 2895499812898633413355829)
              ·
                refine ⟨271453107459246882502109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2895499812898633413355829 271453107459246882502109)
                ·
                  refine ⟨101794915297217580938291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271453107459246882502109 101794915297217580938291)
                  ·
                    rfl

theorem cell21_446051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 3].length) (baseStart_446051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446051 prefixEnd_446051 := by exact prefixLift 446051
  have htrace : WordTrace (prefixWord ++ tailWord_446051) baseStart_446051 baseEnd_446051 := by
    simpa [prefixWord, tailWord_446051, baseEnd_446051] using wordTrace_append hprefix tailTrace_446051
  have hstable : (prefixWord ++ tailWord_446051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446051).length < 2 ^ (prefixWord ++ tailWord_446051).sum := by decide
  have hdescent : baseEnd_446051 < baseStart_446051 := by decide
  rcases family_descends (prefixWord ++ tailWord_446051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446141 : List Nat := [1, 4, 1, 2, 1, 2, 3, 3, 4]
def baseStart_446141 : Nat := 118140960795 + 446141 * 2 ^ 59
def prefixEnd_446141 : Nat := 4983230072969 + 3 ^ 40 * 446141 * 2
def baseEnd_446141 : Nat := 101815454523397424438107

theorem tailTrace_446141 : CollatzResearch.WordTrace tailWord_446141 prefixEnd_446141 101815454523397424438107 := by
  unfold tailWord_446141
  simp only [CollatzResearch.WordTrace]
  refine ⟨16272099076714826661730277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10848066051143217774486851 16272099076714826661730277)
  ·
    refine ⟨3051018576884029999074427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16272099076714826661730277 3051018576884029999074427)
    ·
      refine ⟨4576527865326044998611641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3051018576884029999074427 4576527865326044998611641)
      ·
        refine ⟨3432395898994533748958731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4576527865326044998611641 3432395898994533748958731)
        ·
          refine ⟨5148593848491800623438097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3432395898994533748958731 5148593848491800623438097)
          ·
            refine ⟨3861445386368850467578573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5148593848491800623438097 3861445386368850467578573)
            ·
              refine ⟨1448042019888318925341965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3861445386368850467578573 1448042019888318925341965)
              ·
                refine ⟨543015757458119597003237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1448042019888318925341965 543015757458119597003237)
                ·
                  refine ⟨101815454523397424438107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 543015757458119597003237 101815454523397424438107)
                  ·
                    rfl

theorem cell21_446141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_446141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446141 prefixEnd_446141 := by exact prefixLift 446141
  have htrace : WordTrace (prefixWord ++ tailWord_446141) baseStart_446141 baseEnd_446141 := by
    simpa [prefixWord, tailWord_446141, baseEnd_446141] using wordTrace_append hprefix tailTrace_446141
  have hstable : (prefixWord ++ tailWord_446141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446141).length < 2 ^ (prefixWord ++ tailWord_446141).sum := by decide
  have hdescent : baseEnd_446141 < baseStart_446141 := by decide
  rcases family_descends (prefixWord ++ tailWord_446141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446172 : List Nat := [2, 2, 5, 1, 2, 9]
def baseStart_446172 : Nat := 118140960795 + 446172 * 2 ^ 59
def prefixEnd_446172 : Nat := 4983230072969 + 3 ^ 40 * 446172 * 2
def baseEnd_446172 : Nat := 3771204783175861460051

theorem tailTrace_446172 : CollatzResearch.WordTrace tailWord_446172 prefixEnd_446172 3771204783175861460051 := by
  unfold tailWord_446172
  simp only [CollatzResearch.WordTrace]
  refine ⟨8136614869801259478054385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10848819826401679304072513 8136614869801259478054385)
  ·
    refine ⟨6102461152350944608540789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8136614869801259478054385 6102461152350944608540789)
    ·
      refine ⟨572105733032901057050699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6102461152350944608540789 572105733032901057050699)
      ·
        refine ⟨858158599549351585576049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572105733032901057050699 858158599549351585576049)
        ·
          refine ⟨643618949662013689182037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 858158599549351585576049 643618949662013689182037)
          ·
            refine ⟨3771204783175861460051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 643618949662013689182037 3771204783175861460051)
            ·
              rfl

theorem cell21_446172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 9].length) (baseStart_446172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446172 prefixEnd_446172 := by exact prefixLift 446172
  have htrace : WordTrace (prefixWord ++ tailWord_446172) baseStart_446172 baseEnd_446172 := by
    simpa [prefixWord, tailWord_446172, baseEnd_446172] using wordTrace_append hprefix tailTrace_446172
  have hstable : (prefixWord ++ tailWord_446172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446172).length < 2 ^ (prefixWord ++ tailWord_446172).sum := by decide
  have hdescent : baseEnd_446172 < baseStart_446172 := by decide
  rcases family_descends (prefixWord ++ tailWord_446172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446231 : List Nat := [1, 1, 3, 4, 2, 2, 8]
def baseStart_446231 : Nat := 118140960795 + 446231 * 2 ^ 59
def prefixEnd_446231 : Nat := 4983230072969 + 3 ^ 40 * 446231 * 2
def baseEnd_446231 : Nat := 11315110416619696437547

theorem tailTrace_446231 : CollatzResearch.WordTrace tailWord_446231 prefixEnd_446231 11315110416619696437547 := by
  unfold tailWord_446231
  simp only [CollatzResearch.WordTrace]
  refine ⟨16275381646388772032506547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10850254430925848021671031 16275381646388772032506547)
  ·
    refine ⟨24413072469583158048759821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16275381646388772032506547 24413072469583158048759821)
    ·
      refine ⟨9154902176093684268284933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24413072469583158048759821 9154902176093684268284933)
      ·
        refine ⟨1716544158017565800303425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9154902176093684268284933 1716544158017565800303425)
        ·
          refine ⟨1287408118513174350227569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1716544158017565800303425 1287408118513174350227569)
          ·
            refine ⟨965556088884880762670677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1287408118513174350227569 965556088884880762670677)
            ·
              refine ⟨11315110416619696437547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 965556088884880762670677 11315110416619696437547)
              ·
                rfl

theorem cell21_446231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 8].length) (baseStart_446231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446231 prefixEnd_446231 := by exact prefixLift 446231
  have htrace : WordTrace (prefixWord ++ tailWord_446231) baseStart_446231 baseEnd_446231 := by
    simpa [prefixWord, tailWord_446231, baseEnd_446231] using wordTrace_append hprefix tailTrace_446231
  have hstable : (prefixWord ++ tailWord_446231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446231).length < 2 ^ (prefixWord ++ tailWord_446231).sum := by decide
  have hdescent : baseEnd_446231 < baseStart_446231 := by decide
  rcases family_descends (prefixWord ++ tailWord_446231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446234 : List Nat := [3, 1, 1, 3, 2, 4, 1, 2, 4]
def baseStart_446234 : Nat := 118140960795 + 446234 * 2 ^ 59
def prefixEnd_446234 : Nat := 4983230072969 + 3 ^ 40 * 446234 * 2
def baseEnd_446234 : Nat := 101836678390449929387917

theorem tailTrace_446234 : CollatzResearch.WordTrace tailWord_446234 prefixEnd_446234 101836678390449929387917 := by
  unfold tailWord_446234
  simp only [CollatzResearch.WordTrace]
  refine ⟨4068872766344475886216439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10850327376918602363243837 4068872766344475886216439)
  ·
    refine ⟨6103309149516713829324659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4068872766344475886216439 6103309149516713829324659)
    ·
      refine ⟨9154963724275070743986989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6103309149516713829324659 9154963724275070743986989)
      ·
        refine ⟨3433111396603151528995121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9154963724275070743986989 3433111396603151528995121)
        ·
          refine ⟨2574833547452363646746341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3433111396603151528995121 2574833547452363646746341)
          ·
            refine ⟨482781290147318183764939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2574833547452363646746341 482781290147318183764939)
            ·
              refine ⟨724171935220977275647409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482781290147318183764939 724171935220977275647409)
              ·
                refine ⟨543128951415732956735557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724171935220977275647409 543128951415732956735557)
                ·
                  refine ⟨101836678390449929387917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 543128951415732956735557 101836678390449929387917)
                  ·
                    rfl

theorem cell21_446234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_446234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446234 prefixEnd_446234 := by exact prefixLift 446234
  have htrace : WordTrace (prefixWord ++ tailWord_446234) baseStart_446234 baseEnd_446234 := by
    simpa [prefixWord, tailWord_446234, baseEnd_446234] using wordTrace_append hprefix tailTrace_446234
  have hstable : (prefixWord ++ tailWord_446234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446234).length < 2 ^ (prefixWord ++ tailWord_446234).sum := by decide
  have hdescent : baseEnd_446234 < baseStart_446234 := by decide
  rcases family_descends (prefixWord ++ tailWord_446234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446279 : List Nat := [1, 1, 4, 1, 2, 1, 5, 3, 3]
def baseStart_446279 : Nat := 118140960795 + 446279 * 2 ^ 59
def prefixEnd_446279 : Nat := 4983230072969 + 3 ^ 40 * 446279 * 2
def baseEnd_446279 : Nat := 101846948003539851137825

theorem tailTrace_446279 : CollatzResearch.WordTrace tailWord_446279 prefixEnd_446279 101846948003539851137825 := by
  unfold tailWord_446279
  simp only [CollatzResearch.WordTrace]
  refine ⟨16277132350214876230253891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10851421566809917486835927 16277132350214876230253891)
  ·
    refine ⟨24415698525322314345380837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16277132350214876230253891 24415698525322314345380837)
    ·
      refine ⟨4577943473497933939758907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24415698525322314345380837 4577943473497933939758907)
      ·
        refine ⟨6866915210246900909638361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4577943473497933939758907 6866915210246900909638361)
        ·
          refine ⟨5150186407685175682228771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6866915210246900909638361 5150186407685175682228771)
          ·
            refine ⟨7725279611527763523343157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5150186407685175682228771 7725279611527763523343157)
            ·
              refine ⟨724244963580727830313421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7725279611527763523343157 724244963580727830313421)
              ·
                refine ⟨271591861342772936367533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 724244963580727830313421 271591861342772936367533)
                ·
                  refine ⟨101846948003539851137825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271591861342772936367533 101846948003539851137825)
                  ·
                    rfl

theorem cell21_446279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 3].length) (baseStart_446279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446279 prefixEnd_446279 := by exact prefixLift 446279
  have htrace : WordTrace (prefixWord ++ tailWord_446279) baseStart_446279 baseEnd_446279 := by
    simpa [prefixWord, tailWord_446279, baseEnd_446279] using wordTrace_append hprefix tailTrace_446279
  have hstable : (prefixWord ++ tailWord_446279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446279).length < 2 ^ (prefixWord ++ tailWord_446279).sum := by decide
  have hdescent : baseEnd_446279 < baseStart_446279 := by decide
  rcases family_descends (prefixWord ++ tailWord_446279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446321 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 7]
def baseStart_446321 : Nat := 118140960795 + 446321 * 2 ^ 59
def prefixEnd_446321 : Nat := 4983230072969 + 3 ^ 40 * 446321 * 2
def baseEnd_446321 : Nat := 101856532975757111437739

theorem tailTrace_446321 : CollatzResearch.WordTrace tailWord_446321 prefixEnd_446321 101856532975757111437739 := by
  unfold tailWord_446321
  simp only [CollatzResearch.WordTrace]
  refine ⟨16278664216062717403282817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10852442810708478268855211 16278664216062717403282817)
  ·
    refine ⟨12208998162047038052462113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16278664216062717403282817 12208998162047038052462113)
    ·
      refine ⟨9156748621535278539346585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12208998162047038052462113 9156748621535278539346585)
      ·
        refine ⟨6867561466151458904509939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9156748621535278539346585 6867561466151458904509939)
        ·
          refine ⟨10301342199227188356764909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6867561466151458904509939 10301342199227188356764909)
          ·
            refine ⟨3863003324710195633786841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10301342199227188356764909 3863003324710195633786841)
            ·
              refine ⟨2897252493532646725340131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3863003324710195633786841 2897252493532646725340131)
              ·
                refine ⟨4345878740298970088010197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2897252493532646725340131 4345878740298970088010197)
                ·
                  refine ⟨101856532975757111437739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4345878740298970088010197 101856532975757111437739)
                  ·
                    rfl

theorem cell21_446321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_446321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446321 prefixEnd_446321 := by exact prefixLift 446321
  have htrace : WordTrace (prefixWord ++ tailWord_446321) baseStart_446321 baseEnd_446321 := by
    simpa [prefixWord, tailWord_446321, baseEnd_446321] using wordTrace_append hprefix tailTrace_446321
  have hstable : (prefixWord ++ tailWord_446321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446321).length < 2 ^ (prefixWord ++ tailWord_446321).sum := by decide
  have hdescent : baseEnd_446321 < baseStart_446321 := by decide
  rcases family_descends (prefixWord ++ tailWord_446321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446352 : List Nat := [2, 1, 1, 1, 1, 1, 2, 8, 4]
def baseStart_446352 : Nat := 118140960795 + 446352 * 2 ^ 59
def prefixEnd_446352 : Nat := 4983230072969 + 3 ^ 40 * 446352 * 2
def baseEnd_446352 : Nat := 101863607598107946421009

theorem tailTrace_446352 : CollatzResearch.WordTrace tailWord_446352 prefixEnd_446352 101863607598107946421009 := by
  unfold tailWord_446352
  simp only [CollatzResearch.WordTrace]
  refine ⟨8139897439475204848830655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10853196585966939798440873 8139897439475204848830655)
  ·
    refine ⟨12209846159212807273245983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8139897439475204848830655 12209846159212807273245983)
    ·
      refine ⟨18314769238819210909868975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12209846159212807273245983 18314769238819210909868975)
      ·
        refine ⟨27472153858228816364803463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18314769238819210909868975 27472153858228816364803463)
        ·
          refine ⟨41208230787343224547205195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27472153858228816364803463 41208230787343224547205195)
          ·
            refine ⟨61812346181014836820807793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41208230787343224547205195 61812346181014836820807793)
            ·
              refine ⟨46359259635761127615605845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61812346181014836820807793 46359259635761127615605845)
              ·
                refine ⟨543272573856575714245381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 46359259635761127615605845 543272573856575714245381)
                ·
                  refine ⟨101863607598107946421009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 543272573856575714245381 101863607598107946421009)
                  ·
                    rfl

theorem cell21_446352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_446352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446352 prefixEnd_446352 := by exact prefixLift 446352
  have htrace : WordTrace (prefixWord ++ tailWord_446352) baseStart_446352 baseEnd_446352 := by
    simpa [prefixWord, tailWord_446352, baseEnd_446352] using wordTrace_append hprefix tailTrace_446352
  have hstable : (prefixWord ++ tailWord_446352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446352).length < 2 ^ (prefixWord ++ tailWord_446352).sum := by decide
  have hdescent : baseEnd_446352 < baseStart_446352 := by decide
  rcases family_descends (prefixWord ++ tailWord_446352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446383 : List Nat := [1, 1, 2, 1, 2, 2, 7, 5]
def baseStart_446383 : Nat := 118140960795 + 446383 * 2 ^ 59
def prefixEnd_446383 : Nat := 4983230072969 + 3 ^ 40 * 446383 * 2
def baseEnd_446383 : Nat := 33956894073486260468093

theorem tailTrace_446383 : CollatzResearch.WordTrace tailWord_446383 prefixEnd_446383 33956894073486260468093 := by
  unfold tailWord_446383
  simp only [CollatzResearch.WordTrace]
  refine ⟨16280925541838101992039803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10853950361225401328026535 16280925541838101992039803)
  ·
    refine ⟨24421388312757152988059705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16280925541838101992039803 24421388312757152988059705)
    ·
      refine ⟨18316041234567864741044779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24421388312757152988059705 18316041234567864741044779)
      ·
        refine ⟨27474061851851797111567169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18316041234567864741044779 27474061851851797111567169)
        ·
          refine ⟨20605546388888847833675377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27474061851851797111567169 20605546388888847833675377)
          ·
            refine ⟨15454159791666635875256533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20605546388888847833675377 15454159791666635875256533)
            ·
              refine ⟨362206870117186778326325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 15454159791666635875256533 362206870117186778326325)
              ·
                refine ⟨33956894073486260468093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 362206870117186778326325 33956894073486260468093)
                ·
                  rfl

theorem cell21_446383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 5].length) (baseStart_446383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446383 prefixEnd_446383 := by exact prefixLift 446383
  have htrace : WordTrace (prefixWord ++ tailWord_446383) baseStart_446383 baseEnd_446383 := by
    simpa [prefixWord, tailWord_446383, baseEnd_446383] using wordTrace_append hprefix tailTrace_446383
  have hstable : (prefixWord ++ tailWord_446383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446383).length < 2 ^ (prefixWord ++ tailWord_446383).sum := by decide
  have hdescent : baseEnd_446383 < baseStart_446383 := by decide
  rcases family_descends (prefixWord ++ tailWord_446383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446414 : List Nat := [4, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_446414 : Nat := 118140960795 + 446414 * 2 ^ 59
def prefixEnd_446414 : Nat := 4983230072969 + 3 ^ 40 * 446414 * 2
def baseEnd_446414 : Nat := 101877756842809616387549

theorem tailTrace_446414 : CollatzResearch.WordTrace tailWord_446414 prefixEnd_446414 101877756842809616387549 := by
  unfold tailWord_446414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2035257025590724285802287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10854704136483862857612197 2035257025590724285802287)
  ·
    refine ⟨3052885538386086428703431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2035257025590724285802287 3052885538386086428703431)
    ·
      refine ⟨4579328307579129643055147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3052885538386086428703431 4579328307579129643055147)
      ·
        refine ⟨6868992461368694464582721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4579328307579129643055147 6868992461368694464582721)
        ·
          refine ⟨5151744346026520848437041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6868992461368694464582721 5151744346026520848437041)
          ·
            refine ⟨3863808259519890636327781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5151744346026520848437041 3863808259519890636327781)
            ·
              refine ⟨724464048659979494311459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3863808259519890636327781 724464048659979494311459)
              ·
                refine ⟨1086696072989969241467189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724464048659979494311459 1086696072989969241467189)
                ·
                  refine ⟨101877756842809616387549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1086696072989969241467189 101877756842809616387549)
                  ·
                    rfl

theorem cell21_446414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_446414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446414 prefixEnd_446414 := by exact prefixLift 446414
  have htrace : WordTrace (prefixWord ++ tailWord_446414) baseStart_446414 baseEnd_446414 := by
    simpa [prefixWord, tailWord_446414, baseEnd_446414] using wordTrace_append hprefix tailTrace_446414
  have hstable : (prefixWord ++ tailWord_446414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446414).length < 2 ^ (prefixWord ++ tailWord_446414).sum := by decide
  have hdescent : baseEnd_446414 < baseStart_446414 := by decide
  rcases family_descends (prefixWord ++ tailWord_446414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446434 : List Nat := [3, 3, 3, 1, 2, 2, 2, 5]
def baseStart_446434 : Nat := 118140960795 + 446434 * 2 ^ 59
def prefixEnd_446434 : Nat := 4983230072969 + 3 ^ 40 * 446434 * 2
def baseEnd_446434 : Nat := 33960773705098008684725

theorem tailTrace_446434 : CollatzResearch.WordTrace tailWord_446434 prefixEnd_446434 33960773705098008684725 := by
  unfold tailWord_446434
  simp only [CollatzResearch.WordTrace]
  refine ⟨4070696416163334425536589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10855190443102225134764237 4070696416163334425536589)
  ·
    refine ⟨1526511156061250409576221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4070696416163334425536589 1526511156061250409576221)
    ·
      refine ⟨572441683522968903591083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1526511156061250409576221 572441683522968903591083)
      ·
        refine ⟨858662525284453355386625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572441683522968903591083 858662525284453355386625)
        ·
          refine ⟨643996893963340016539969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 858662525284453355386625 643996893963340016539969)
          ·
            refine ⟨482997670472505012404977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 643996893963340016539969 482997670472505012404977)
            ·
              refine ⟨362248252854378759303733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482997670472505012404977 362248252854378759303733)
              ·
                refine ⟨33960773705098008684725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 362248252854378759303733 33960773705098008684725)
                ·
                  rfl

theorem cell21_446434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_446434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446434 prefixEnd_446434 := by exact prefixLift 446434
  have htrace : WordTrace (prefixWord ++ tailWord_446434) baseStart_446434 baseEnd_446434 := by
    simpa [prefixWord, tailWord_446434, baseEnd_446434] using wordTrace_append hprefix tailTrace_446434
  have hstable : (prefixWord ++ tailWord_446434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446434).length < 2 ^ (prefixWord ++ tailWord_446434).sum := by decide
  have hdescent : baseEnd_446434 < baseStart_446434 := by decide
  rcases family_descends (prefixWord ++ tailWord_446434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446549 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 7]
def baseStart_446549 : Nat := 118140960795 + 446549 * 2 ^ 59
def prefixEnd_446549 : Nat := 4983230072969 + 3 ^ 40 * 446549 * 2
def baseEnd_446549 : Nat := 101908565682079381637273

theorem tailTrace_446549 : CollatzResearch.WordTrace tailWord_446549 prefixEnd_446549 101908565682079381637273 := by
  unfold tailWord_446549
  simp only [CollatzResearch.WordTrace]
  refine ⟨16286980059236712342582701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10857986706157808228388467 16286980059236712342582701)
  ·
    refine ⟨6107617522213767128468513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16286980059236712342582701 6107617522213767128468513)
    ·
      refine ⟨4580713141660325346351385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6107617522213767128468513 4580713141660325346351385)
      ·
        refine ⟨3435534856245244009763539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4580713141660325346351385 3435534856245244009763539)
        ·
          refine ⟨5153302284367866014645309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3435534856245244009763539 5153302284367866014645309)
          ·
            refine ⟨1932488356637949755491991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5153302284367866014645309 1932488356637949755491991)
            ·
              refine ⟨2898732534956924633237987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1932488356637949755491991 2898732534956924633237987)
              ·
                refine ⟨4348098802435386949856981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2898732534956924633237987 4348098802435386949856981)
                ·
                  refine ⟨101908565682079381637273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4348098802435386949856981 101908565682079381637273)
                  ·
                    rfl

theorem cell21_446549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_446549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446549 prefixEnd_446549 := by exact prefixLift 446549
  have htrace : WordTrace (prefixWord ++ tailWord_446549) baseStart_446549 baseEnd_446549 := by
    simpa [prefixWord, tailWord_446549, baseEnd_446549] using wordTrace_append hprefix tailTrace_446549
  have hstable : (prefixWord ++ tailWord_446549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446549).length < 2 ^ (prefixWord ++ tailWord_446549).sum := by decide
  have hdescent : baseEnd_446549 < baseStart_446549 := by decide
  rcases family_descends (prefixWord ++ tailWord_446549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446558 : List Nat := [4, 4, 1, 1, 2, 1, 2, 3, 3]
def baseStart_446558 : Nat := 118140960795 + 446558 * 2 ^ 59
def prefixEnd_446558 : Nat := 4983230072969 + 3 ^ 40 * 446558 * 2
def baseEnd_446558 : Nat := 101910619604697365987255

theorem tailTrace_446558 : CollatzResearch.WordTrace tailWord_446558 prefixEnd_446558 101910619604697365987255 := by
  unfold tailWord_446558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2035913539525513359957541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10858205544136071253106885 2035913539525513359957541)
  ·
    refine ⟨381733788661033754992039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2035913539525513359957541 381733788661033754992039)
    ·
      refine ⟨572600682991550632488059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381733788661033754992039 572600682991550632488059)
      ·
        refine ⟨858901024487325948732089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572600682991550632488059 858901024487325948732089)
        ·
          refine ⟨644175768365494461549067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 858901024487325948732089 644175768365494461549067)
          ·
            refine ⟨966263652548241692323601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644175768365494461549067 966263652548241692323601)
            ·
              refine ⟨724697739411181269242701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 966263652548241692323601 724697739411181269242701)
              ·
                refine ⟨271761652279192975966013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 724697739411181269242701 271761652279192975966013)
                ·
                  refine ⟨101910619604697365987255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271761652279192975966013 101910619604697365987255)
                  ·
                    rfl

theorem cell21_446558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_446558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446558 prefixEnd_446558 := by exact prefixLift 446558
  have htrace : WordTrace (prefixWord ++ tailWord_446558) baseStart_446558 baseEnd_446558 := by
    simpa [prefixWord, tailWord_446558, baseEnd_446558] using wordTrace_append hprefix tailTrace_446558
  have hstable : (prefixWord ++ tailWord_446558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446558).length < 2 ^ (prefixWord ++ tailWord_446558).sum := by decide
  have hdescent : baseEnd_446558 < baseStart_446558 := by decide
  rcases family_descends (prefixWord ++ tailWord_446558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446628 : List Nat := [2, 3, 1, 2, 5, 1, 7]
def baseStart_446628 : Nat := 118140960795 + 446628 * 2 ^ 59
def prefixEnd_446628 : Nat := 4983230072969 + 3 ^ 40 * 446628 * 2
def baseEnd_446628 : Nat := 11325177173154755535605

theorem tailTrace_446628 : CollatzResearch.WordTrace tailWord_446628 prefixEnd_446628 11325177173154755535605 := by
  unfold tailWord_446628
  simp only [CollatzResearch.WordTrace]
  refine ⟨8144930712975254417354269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10859907617300339223139025 8144930712975254417354269)
  ·
    refine ⟨3054349017365720406507851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8144930712975254417354269 3054349017365720406507851)
    ·
      refine ⟨4581523526048580609761777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3054349017365720406507851 4581523526048580609761777)
      ·
        refine ⟨3436142644536435457321333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4581523526048580609761777 3436142644536435457321333)
        ·
          refine ⟨322138372925290824123875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3436142644536435457321333 322138372925290824123875)
          ·
            refine ⟨483207559387936236185813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322138372925290824123875 483207559387936236185813)
            ·
              refine ⟨11325177173154755535605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 483207559387936236185813 11325177173154755535605)
              ·
                rfl

theorem cell21_446628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 7].length) (baseStart_446628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446628 prefixEnd_446628 := by exact prefixLift 446628
  have htrace : WordTrace (prefixWord ++ tailWord_446628) baseStart_446628 baseEnd_446628 := by
    simpa [prefixWord, tailWord_446628, baseEnd_446628] using wordTrace_append hprefix tailTrace_446628
  have hstable : (prefixWord ++ tailWord_446628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446628).length < 2 ^ (prefixWord ++ tailWord_446628).sum := by decide
  have hdescent : baseEnd_446628 < baseStart_446628 := by decide
  rcases family_descends (prefixWord ++ tailWord_446628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446718 : List Nat := [4, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_446718 : Nat := 118140960795 + 446718 * 2 ^ 59
def prefixEnd_446718 : Nat := 4983230072969 + 3 ^ 40 * 446718 * 2
def baseEnd_446718 : Nat := 101947133784572643320261

theorem tailTrace_446718 : CollatzResearch.WordTrace tailWord_446718 prefixEnd_446718 101947133784572643320261 := by
  unfold tailWord_446718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2036642999453056775685601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10862095997082969470323205 2036642999453056775685601)
  ·
    refine ⟨1527482249589792581764201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2036642999453056775685601 1527482249589792581764201)
    ·
      refine ⟨1145611687192344436323151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1527482249589792581764201 1145611687192344436323151)
      ·
        refine ⟨1718417530788516654484727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1145611687192344436323151 1718417530788516654484727)
        ·
          refine ⟨2577626296182774981727091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1718417530788516654484727 2577626296182774981727091)
          ·
            refine ⟨3866439444274162472590637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577626296182774981727091 3866439444274162472590637)
            ·
              refine ⟨1449914791602810927221489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3866439444274162472590637 1449914791602810927221489)
              ·
                refine ⟨1087436093702108195416117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1449914791602810927221489 1087436093702108195416117)
                ·
                  refine ⟨101947133784572643320261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1087436093702108195416117 101947133784572643320261)
                  ·
                    rfl

theorem cell21_446718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_446718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446718 prefixEnd_446718 := by exact prefixLift 446718
  have htrace : WordTrace (prefixWord ++ tailWord_446718) baseStart_446718 baseEnd_446718 := by
    simpa [prefixWord, tailWord_446718, baseEnd_446718] using wordTrace_append hprefix tailTrace_446718
  have hstable : (prefixWord ++ tailWord_446718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446718).length < 2 ^ (prefixWord ++ tailWord_446718).sum := by decide
  have hdescent : baseEnd_446718 < baseStart_446718 := by decide
  rcases family_descends (prefixWord ++ tailWord_446718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446749 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 6]
def baseStart_446749 : Nat := 118140960795 + 446749 * 2 ^ 59
def prefixEnd_446749 : Nat := 4983230072969 + 3 ^ 40 * 446749 * 2
def baseEnd_446749 : Nat := 101954208406923478303531

theorem tailTrace_446749 : CollatzResearch.WordTrace tailWord_446749 prefixEnd_446749 101954208406923478303531 := by
  unfold tailWord_446749
  simp only [CollatzResearch.WordTrace]
  refine ⟨16294274658512146499863301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10862849772341430999908867 16294274658512146499863301)
  ·
    refine ⟨3055176498471027468724369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16294274658512146499863301 3055176498471027468724369)
    ·
      refine ⟨2291382373853270601543277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3055176498471027468724369 2291382373853270601543277)
      ·
        refine ⟨859268390194976475578729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2291382373853270601543277 859268390194976475578729)
        ·
          refine ⟨644451292646232356684047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 859268390194976475578729 644451292646232356684047)
          ·
            refine ⟨966676938969348535026071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644451292646232356684047 966676938969348535026071)
            ·
              refine ⟨1450015408454022802539107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966676938969348535026071 1450015408454022802539107)
              ·
                refine ⟨2175023112681034203808661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450015408454022802539107 2175023112681034203808661)
                ·
                  refine ⟨101954208406923478303531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2175023112681034203808661 101954208406923478303531)
                  ·
                    rfl

theorem cell21_446749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_446749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446749 prefixEnd_446749 := by exact prefixLift 446749
  have htrace : WordTrace (prefixWord ++ tailWord_446749) baseStart_446749 baseEnd_446749 := by
    simpa [prefixWord, tailWord_446749, baseEnd_446749] using wordTrace_append hprefix tailTrace_446749
  have hstable : (prefixWord ++ tailWord_446749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446749).length < 2 ^ (prefixWord ++ tailWord_446749).sum := by decide
  have hdescent : baseEnd_446749 < baseStart_446749 := by decide
  rcases family_descends (prefixWord ++ tailWord_446749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446791 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 8]
def baseStart_446791 : Nat := 118140960795 + 446791 * 2 ^ 59
def prefixEnd_446791 : Nat := 4983230072969 + 3 ^ 40 * 446791 * 2
def baseEnd_446791 : Nat := 101963793379140738603445

theorem tailTrace_446791 : CollatzResearch.WordTrace tailWord_446791 prefixEnd_446791 101963793379140738603445 := by
  unfold tailWord_446791
  simp only [CollatzResearch.WordTrace]
  refine ⟨16295806524359987672892227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10863871016239991781928151 16295806524359987672892227)
  ·
    refine ⟨24443709786539981509338341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16295806524359987672892227 24443709786539981509338341)
    ·
      refine ⟨4583195584976246533000939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24443709786539981509338341 4583195584976246533000939)
      ·
        refine ⟨6874793377464369799501409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4583195584976246533000939 6874793377464369799501409)
        ·
          refine ⟨5156095033098277349626057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6874793377464369799501409 5156095033098277349626057)
          ·
            refine ⟨3867071274823708012219543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5156095033098277349626057 3867071274823708012219543)
            ·
              refine ⟨5800606912235562018329315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3867071274823708012219543 5800606912235562018329315)
              ·
                refine ⟨8700910368353343027493973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5800606912235562018329315 8700910368353343027493973)
                ·
                  refine ⟨101963793379140738603445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8700910368353343027493973 101963793379140738603445)
                  ·
                    rfl

theorem cell21_446791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 8].length) (baseStart_446791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446791 prefixEnd_446791 := by exact prefixLift 446791
  have htrace : WordTrace (prefixWord ++ tailWord_446791) baseStart_446791 baseEnd_446791 := by
    simpa [prefixWord, tailWord_446791, baseEnd_446791] using wordTrace_append hprefix tailTrace_446791
  have hstable : (prefixWord ++ tailWord_446791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446791).length < 2 ^ (prefixWord ++ tailWord_446791).sum := by decide
  have hdescent : baseEnd_446791 < baseStart_446791 := by decide
  rcases family_descends (prefixWord ++ tailWord_446791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446884 : List Nat := [2, 3, 1, 2, 1, 1, 4, 3, 4]
def baseStart_446884 : Nat := 118140960795 + 446884 * 2 ^ 59
def prefixEnd_446884 : Nat := 4983230072969 + 3 ^ 40 * 446884 * 2
def baseEnd_446884 : Nat := 101985017246193243553255

theorem tailTrace_446884 : CollatzResearch.WordTrace tailWord_446884 prefixEnd_446884 101985017246193243553255 := by
  unfold tailWord_446884
  simp only [CollatzResearch.WordTrace]
  refine ⟨8149599256511532278013853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10866132342015376370685137 8149599256511532278013853)
  ·
    refine ⟨3056099721191824604255195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8149599256511532278013853 3056099721191824604255195)
    ·
      refine ⟨4584149581787736906382793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3056099721191824604255195 4584149581787736906382793)
      ·
        refine ⟨3438112186340802679787095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4584149581787736906382793 3438112186340802679787095)
        ·
          refine ⟨5157168279511204019680643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3438112186340802679787095 5157168279511204019680643)
          ·
            refine ⟨7735752419266806029520965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5157168279511204019680643 7735752419266806029520965)
            ·
              refine ⟨1450453578612526130535181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7735752419266806029520965 1450453578612526130535181)
              ·
                refine ⟨543920091979697298950693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1450453578612526130535181 543920091979697298950693)
                ·
                  refine ⟨101985017246193243553255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 543920091979697298950693 101985017246193243553255)
                  ·
                    rfl

theorem cell21_446884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_446884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446884 prefixEnd_446884 := by exact prefixLift 446884
  have htrace : WordTrace (prefixWord ++ tailWord_446884) baseStart_446884 baseEnd_446884 := by
    simpa [prefixWord, tailWord_446884, baseEnd_446884] using wordTrace_append hprefix tailTrace_446884
  have hstable : (prefixWord ++ tailWord_446884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446884).length < 2 ^ (prefixWord ++ tailWord_446884).sum := by decide
  have hdescent : baseEnd_446884 < baseStart_446884 := by decide
  rcases family_descends (prefixWord ++ tailWord_446884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446890 : List Nat := [3, 1, 6, 1, 1, 1, 3, 5]
def baseStart_446890 : Nat := 118140960795 + 446890 * 2 ^ 59
def prefixEnd_446890 : Nat := 4983230072969 + 3 ^ 40 * 446890 * 2
def baseEnd_446890 : Nat := 33995462175979522151081

theorem tailTrace_446890 : CollatzResearch.WordTrace tailWord_446890 prefixEnd_446890 33995462175979522151081 := by
  unfold tailWord_446890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4074854337750331895186531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10866278234000885053830749 4074854337750331895186531)
  ·
    refine ⟨6112281506625497842779797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4074854337750331895186531 6112281506625497842779797)
    ·
      refine ⟨286513195623070211380303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6112281506625497842779797 286513195623070211380303)
      ·
        refine ⟨429769793434605317070455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286513195623070211380303 429769793434605317070455)
        ·
          refine ⟨644654690151907975605683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429769793434605317070455 644654690151907975605683)
          ·
            refine ⟨966982035227861963408525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644654690151907975605683 966982035227861963408525)
            ·
              refine ⟨362618263210448236278197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 966982035227861963408525 362618263210448236278197)
              ·
                refine ⟨33995462175979522151081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 362618263210448236278197 33995462175979522151081)
                ·
                  rfl

theorem cell21_446890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_446890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446890 prefixEnd_446890 := by exact prefixLift 446890
  have htrace : WordTrace (prefixWord ++ tailWord_446890) baseStart_446890 baseEnd_446890 := by
    simpa [prefixWord, tailWord_446890, baseEnd_446890] using wordTrace_append hprefix tailTrace_446890
  have hstable : (prefixWord ++ tailWord_446890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446890).length < 2 ^ (prefixWord ++ tailWord_446890).sum := by decide
  have hdescent : baseEnd_446890 < baseStart_446890 := by decide
  rcases family_descends (prefixWord ++ tailWord_446890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446912 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 9]
def baseStart_446912 : Nat := 118140960795 + 446912 * 2 ^ 59
def prefixEnd_446912 : Nat := 4983230072969 + 3 ^ 40 * 446912 * 2
def baseEnd_446912 : Nat := 101991407227671417086531

theorem tailTrace_446912 : CollatzResearch.WordTrace tailWord_446912 prefixEnd_446912 101991407227671417086531 := by
  unfold tailWord_446912
  simp only [CollatzResearch.WordTrace]
  refine ⟨8150109878460812669023495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10866813171281083558697993 8150109878460812669023495)
  ·
    refine ⟨12225164817691219003535243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8150109878460812669023495 12225164817691219003535243)
    ·
      refine ⟨18337747226536828505302865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12225164817691219003535243 18337747226536828505302865)
      ·
        refine ⟨13753310419902621378977149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18337747226536828505302865 13753310419902621378977149)
        ·
          refine ⟨5157491407463483017116431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13753310419902621378977149 5157491407463483017116431)
          ·
            refine ⟨7736237111195224525674647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5157491407463483017116431 7736237111195224525674647)
            ·
              refine ⟨11604355666792836788511971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7736237111195224525674647 11604355666792836788511971)
              ·
                refine ⟨17406533500189255182767957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11604355666792836788511971 17406533500189255182767957)
                ·
                  refine ⟨101991407227671417086531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17406533500189255182767957 101991407227671417086531)
                  ·
                    rfl

theorem cell21_446912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_446912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446912 prefixEnd_446912 := by exact prefixLift 446912
  have htrace : WordTrace (prefixWord ++ tailWord_446912) baseStart_446912 baseEnd_446912 := by
    simpa [prefixWord, tailWord_446912, baseEnd_446912] using wordTrace_append hprefix tailTrace_446912
  have hstable : (prefixWord ++ tailWord_446912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446912).length < 2 ^ (prefixWord ++ tailWord_446912).sum := by decide
  have hdescent : baseEnd_446912 < baseStart_446912 := by decide
  rcases family_descends (prefixWord ++ tailWord_446912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446949 : List Nat := [1, 3, 1, 5, 3, 1, 2, 5]
def baseStart_446949 : Nat := 118140960795 + 446949 * 2 ^ 59
def prefixEnd_446949 : Nat := 4983230072969 + 3 ^ 40 * 446949 * 2
def baseEnd_446949 : Nat := 33999950377255858323263

theorem tailTrace_446949 : CollatzResearch.WordTrace tailWord_446949 prefixEnd_446949 33999950377255858323263 := by
  unfold tailWord_446949
  simp only [CollatzResearch.WordTrace]
  refine ⟨16301569257787580657143901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10867712838525053771429267 16301569257787580657143901)
  ·
    refine ⟨6113088471670342746428963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16301569257787580657143901 6113088471670342746428963)
    ·
      refine ⟨9169632707505514119643445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6113088471670342746428963 9169632707505514119643445)
      ·
        refine ⟨859653066328641948716573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9169632707505514119643445 859653066328641948716573)
        ·
          refine ⟨322369899873240730768715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 859653066328641948716573 322369899873240730768715)
          ·
            refine ⟨483554849809861096153073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322369899873240730768715 483554849809861096153073)
            ·
              refine ⟨362666137357395822114805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483554849809861096153073 362666137357395822114805)
              ·
                refine ⟨33999950377255858323263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 362666137357395822114805 33999950377255858323263)
                ·
                  rfl

theorem cell21_446949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 5].length) (baseStart_446949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446949 prefixEnd_446949 := by exact prefixLift 446949
  have htrace : WordTrace (prefixWord ++ tailWord_446949) baseStart_446949 baseEnd_446949 := by
    simpa [prefixWord, tailWord_446949, baseEnd_446949] using wordTrace_append hprefix tailTrace_446949
  have hstable : (prefixWord ++ tailWord_446949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446949).length < 2 ^ (prefixWord ++ tailWord_446949).sum := by decide
  have hdescent : baseEnd_446949 < baseStart_446949 := by decide
  rcases family_descends (prefixWord ++ tailWord_446949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446980 : List Nat := [2, 3, 2, 3, 1, 2, 3, 2, 3]
def baseStart_446980 : Nat := 118140960795 + 446980 * 2 ^ 59
def prefixEnd_446980 : Nat := 4983230072969 + 3 ^ 40 * 446980 * 2
def baseEnd_446980 : Nat := 102006925754118409953059

theorem tailTrace_446980 : CollatzResearch.WordTrace tailWord_446980 prefixEnd_446980 102006925754118409953059 := by
  unfold tailWord_446980
  simp only [CollatzResearch.WordTrace]
  refine ⟨8151349960337636475761197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10868466613783515301014929 8151349960337636475761197)
  ·
    refine ⟨3056756235126613678410449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8151349960337636475761197 3056756235126613678410449)
    ·
      refine ⟨2292567176344960258807837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3056756235126613678410449 2292567176344960258807837)
      ·
        refine ⟨859712691129360097052939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2292567176344960258807837 859712691129360097052939)
        ·
          refine ⟨1289569036694040145579409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859712691129360097052939 1289569036694040145579409)
          ·
            refine ⟨967176777520530109184557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1289569036694040145579409 967176777520530109184557)
            ·
              refine ⟨362691291570198790944209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 967176777520530109184557 362691291570198790944209)
              ·
                refine ⟨272018468677649093208157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362691291570198790944209 272018468677649093208157)
                ·
                  refine ⟨102006925754118409953059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272018468677649093208157 102006925754118409953059)
                  ·
                    rfl

theorem cell21_446980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_446980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_446980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_446980 prefixEnd_446980 := by exact prefixLift 446980
  have htrace : WordTrace (prefixWord ++ tailWord_446980) baseStart_446980 baseEnd_446980 := by
    simpa [prefixWord, tailWord_446980, baseEnd_446980] using wordTrace_append hprefix tailTrace_446980
  have hstable : (prefixWord ++ tailWord_446980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446980).length < 2 ^ (prefixWord ++ tailWord_446980).sum := by decide
  have hdescent : baseEnd_446980 < baseStart_446980 := by decide
  rcases family_descends (prefixWord ++ tailWord_446980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447036 : List Nat := [2, 2, 2, 2, 3, 1, 1, 4, 4]
def baseStart_447036 : Nat := 118140960795 + 447036 * 2 ^ 59
def prefixEnd_447036 : Nat := 4983230072969 + 3 ^ 40 * 447036 * 2
def baseEnd_447036 : Nat := 102019705717074757019611

theorem tailTrace_447036 : CollatzResearch.WordTrace tailWord_447036 prefixEnd_447036 102019705717074757019611 := by
  unfold tailWord_447036
  simp only [CollatzResearch.WordTrace]
  refine ⟨8152371204236197257780481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10869828272314929677040641 8152371204236197257780481)
  ·
    refine ⟨6114278403177147943335361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8152371204236197257780481 6114278403177147943335361)
    ·
      refine ⟨4585708802382860957501521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6114278403177147943335361 4585708802382860957501521)
      ·
        refine ⟨3439281601787145718126141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4585708802382860957501521 3439281601787145718126141)
        ·
          refine ⟨1289730600670179644297303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3439281601787145718126141 1289730600670179644297303)
          ·
            refine ⟨1934595901005269466445955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1289730600670179644297303 1934595901005269466445955)
            ·
              refine ⟨2901893851507904199668933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1934595901005269466445955 2901893851507904199668933)
              ·
                refine ⟨544105097157732037437925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2901893851507904199668933 544105097157732037437925)
                ·
                  refine ⟨102019705717074757019611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 544105097157732037437925 102019705717074757019611)
                  ·
                    rfl

theorem cell21_447036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_447036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447036 prefixEnd_447036 := by exact prefixLift 447036
  have htrace : WordTrace (prefixWord ++ tailWord_447036) baseStart_447036 baseEnd_447036 := by
    simpa [prefixWord, tailWord_447036, baseEnd_447036] using wordTrace_append hprefix tailTrace_447036
  have hstable : (prefixWord ++ tailWord_447036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447036).length < 2 ^ (prefixWord ++ tailWord_447036).sum := by decide
  have hdescent : baseEnd_447036 < baseStart_447036 := by decide
  rcases family_descends (prefixWord ++ tailWord_447036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447050 : List Nat := [3, 1, 2, 1, 1, 4, 3, 6]
def baseStart_447050 : Nat := 118140960795 + 447050 * 2 ^ 59
def prefixEnd_447050 : Nat := 4983230072969 + 3 ^ 40 * 447050 * 2
def baseEnd_447050 : Nat := 34007633569271281262083

theorem tailTrace_447050 : CollatzResearch.WordTrace tailWord_447050 prefixEnd_447050 34007633569271281262083 := by
  unfold tailWord_447050
  simp only [CollatzResearch.WordTrace]
  refine ⟨4076313257605418726642651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10870168686947783271047069 4076313257605418726642651)
  ·
    refine ⟨6114469886408128089963977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4076313257605418726642651 6114469886408128089963977)
    ·
      refine ⟨4585852414806096067472983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6114469886408128089963977 4585852414806096067472983)
      ·
        refine ⟨6878778622209144101209475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4585852414806096067472983 6878778622209144101209475)
        ·
          refine ⟨10318167933313716151814213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6878778622209144101209475 10318167933313716151814213)
          ·
            refine ⟨1934656487496321778465165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10318167933313716151814213 1934656487496321778465165)
            ·
              refine ⟨725496182811120666924437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1934656487496321778465165 725496182811120666924437)
              ·
                refine ⟨34007633569271281262083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 725496182811120666924437 34007633569271281262083)
                ·
                  rfl

theorem cell21_447050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_447050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447050 prefixEnd_447050 := by exact prefixLift 447050
  have htrace : WordTrace (prefixWord ++ tailWord_447050) baseStart_447050 baseEnd_447050 := by
    simpa [prefixWord, tailWord_447050, baseEnd_447050] using wordTrace_append hprefix tailTrace_447050
  have hstable : (prefixWord ++ tailWord_447050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447050).length < 2 ^ (prefixWord ++ tailWord_447050).sum := by decide
  have hdescent : baseEnd_447050 < baseStart_447050 := by decide
  rcases family_descends (prefixWord ++ tailWord_447050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447053 : List Nat := [1, 6, 1, 1, 2, 1, 2, 3, 4]
def baseStart_447053 : Nat := 118140960795 + 447053 * 2 ^ 59
def prefixEnd_447053 : Nat := 4983230072969 + 3 ^ 40 * 447053 * 2
def baseEnd_447053 : Nat := 102023585348686505236243

theorem tailTrace_447053 : CollatzResearch.WordTrace tailWord_447053 prefixEnd_447053 102023585348686505236243 := by
  unfold tailWord_447053
  simp only [CollatzResearch.WordTrace]
  refine ⟨16305362449410806418929813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10870241632940537612619875 16305362449410806418929813)
  ·
    refine ⟨764313864816131550887335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16305362449410806418929813 764313864816131550887335)
    ·
      refine ⟨1146470797224197326331003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 764313864816131550887335 1146470797224197326331003)
      ·
        refine ⟨1719706195836295989496505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1146470797224197326331003 1719706195836295989496505)
        ·
          refine ⟨1289779646877221992122379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1719706195836295989496505 1289779646877221992122379)
          ·
            refine ⟨1934669470315832988183569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1289779646877221992122379 1934669470315832988183569)
            ·
              refine ⟨1451002102736874741137677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1934669470315832988183569 1451002102736874741137677)
              ·
                refine ⟨544125788526328027926629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1451002102736874741137677 544125788526328027926629)
                ·
                  refine ⟨102023585348686505236243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 544125788526328027926629 102023585348686505236243)
                  ·
                    rfl

theorem cell21_447053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_447053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447053 prefixEnd_447053 := by exact prefixLift 447053
  have htrace : WordTrace (prefixWord ++ tailWord_447053) baseStart_447053 baseEnd_447053 := by
    simpa [prefixWord, tailWord_447053, baseEnd_447053] using wordTrace_append hprefix tailTrace_447053
  have hstable : (prefixWord ++ tailWord_447053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447053).length < 2 ^ (prefixWord ++ tailWord_447053).sum := by decide
  have hdescent : baseEnd_447053 < baseStart_447053 := by decide
  rcases family_descends (prefixWord ++ tailWord_447053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447064 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 7]
def baseStart_447064 : Nat := 118140960795 + 447064 * 2 ^ 59
def prefixEnd_447064 : Nat := 4983230072969 + 3 ^ 40 * 447064 * 2
def baseEnd_447064 : Nat := 102026095698552930552887

theorem tailTrace_447064 : CollatzResearch.WordTrace tailWord_447064 prefixEnd_447064 102026095698552930552887 := by
  unfold tailWord_447064
  simp only [CollatzResearch.WordTrace]
  refine ⟨8152881826185477648790123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10870509101580636865053497 8152881826185477648790123)
  ·
    refine ⟨12229322739278216473185185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8152881826185477648790123 12229322739278216473185185)
    ·
      refine ⟨9171992054458662354888889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12229322739278216473185185 9171992054458662354888889)
      ·
        refine ⟨6878994040843996766166667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9171992054458662354888889 6878994040843996766166667)
        ·
          refine ⟨10318491061265995149250001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6878994040843996766166667 10318491061265995149250001)
          ·
            refine ⟨7738868295949496361937501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10318491061265995149250001 7738868295949496361937501)
            ·
              refine ⟨2902075610981061135726563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7738868295949496361937501 2902075610981061135726563)
              ·
                refine ⟨4353113416471591703589845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2902075610981061135726563 4353113416471591703589845)
                ·
                  refine ⟨102026095698552930552887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4353113416471591703589845 102026095698552930552887)
                  ·
                    rfl

theorem cell21_447064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_447064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447064 prefixEnd_447064 := by exact prefixLift 447064
  have htrace : WordTrace (prefixWord ++ tailWord_447064) baseStart_447064 baseEnd_447064 := by
    simpa [prefixWord, tailWord_447064, baseEnd_447064] using wordTrace_append hprefix tailTrace_447064
  have hstable : (prefixWord ++ tailWord_447064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447064).length < 2 ^ (prefixWord ++ tailWord_447064).sum := by decide
  have hdescent : baseEnd_447064 < baseStart_447064 := by decide
  rcases family_descends (prefixWord ++ tailWord_447064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447185 : List Nat := [1, 2, 2, 1, 2, 3, 1, 9]
def baseStart_447185 : Nat := 118140960795 + 447185 * 2 ^ 59
def prefixEnd_447185 : Nat := 4983230072969 + 3 ^ 40 * 447185 * 2
def baseEnd_447185 : Nat := 34017903182361203011991

theorem tailTrace_447185 : CollatzResearch.WordTrace tailWord_447185 prefixEnd_447185 34017903182361203011991 := by
  unfold tailWord_447185
  simp only [CollatzResearch.WordTrace]
  refine ⟨16310176884932592962735009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10873451256621728641823339 16310176884932592962735009)
  ·
    refine ⟨12232632663699444722051257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16310176884932592962735009 12232632663699444722051257)
    ·
      refine ⟨9174474497774583541538443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12232632663699444722051257 9174474497774583541538443)
      ·
        refine ⟨13761711746661875312307665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9174474497774583541538443 13761711746661875312307665)
        ·
          refine ⟨10321283809996406484230749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13761711746661875312307665 10321283809996406484230749)
          ·
            refine ⟨3870481428748652431586531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10321283809996406484230749 3870481428748652431586531)
            ·
              refine ⟨5805722143122978647379797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3870481428748652431586531 5805722143122978647379797)
              ·
                refine ⟨34017903182361203011991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5805722143122978647379797 34017903182361203011991)
                ·
                  rfl

theorem cell21_447185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 9].length) (baseStart_447185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447185 prefixEnd_447185 := by exact prefixLift 447185
  have htrace : WordTrace (prefixWord ++ tailWord_447185) baseStart_447185 baseEnd_447185 := by
    simpa [prefixWord, tailWord_447185, baseEnd_447185] using wordTrace_append hprefix tailTrace_447185
  have hstable : (prefixWord ++ tailWord_447185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447185).length < 2 ^ (prefixWord ++ tailWord_447185).sum := by decide
  have hdescent : baseEnd_447185 < baseStart_447185 := by decide
  rcases family_descends (prefixWord ++ tailWord_447185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447208 : List Nat := [2, 1, 4, 1, 4, 2, 2, 2, 3]
def baseStart_447208 : Nat := 118140960795 + 447208 * 2 ^ 59
def prefixEnd_447208 : Nat := 4983230072969 + 3 ^ 40 * 447208 * 2
def baseEnd_447208 : Nat := 102058958460440680152593

theorem tailTrace_447208 : CollatzResearch.WordTrace tailWord_447208 prefixEnd_447208 102058958460440680152593 := by
  unfold tailWord_447208
  simp only [CollatzResearch.WordTrace]
  refine ⟨8155507881924633945411139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10874010509232845260548185 8155507881924633945411139)
  ·
    refine ⟨12233261822886950918116709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8155507881924633945411139 12233261822886950918116709)
    ·
      refine ⟨2293736591791303297146883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12233261822886950918116709 2293736591791303297146883)
      ·
        refine ⟨3440604887686954945720325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2293736591791303297146883 3440604887686954945720325)
        ·
          refine ⟨645113416441304052322561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3440604887686954945720325 645113416441304052322561)
          ·
            refine ⟨483835062330978039241921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645113416441304052322561 483835062330978039241921)
            ·
              refine ⟨362876296748233529431441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483835062330978039241921 362876296748233529431441)
              ·
                refine ⟨272157222561175147073581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362876296748233529431441 272157222561175147073581)
                ·
                  refine ⟨102058958460440680152593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272157222561175147073581 102058958460440680152593)
                  ·
                    rfl

theorem cell21_447208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 3].length) (baseStart_447208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447208 prefixEnd_447208 := by exact prefixLift 447208
  have htrace : WordTrace (prefixWord ++ tailWord_447208) baseStart_447208 baseEnd_447208 := by
    simpa [prefixWord, tailWord_447208, baseEnd_447208] using wordTrace_append hprefix tailTrace_447208
  have hstable : (prefixWord ++ tailWord_447208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447208).length < 2 ^ (prefixWord ++ tailWord_447208).sum := by decide
  have hdescent : baseEnd_447208 < baseStart_447208 := by decide
  rcases family_descends (prefixWord ++ tailWord_447208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447216 : List Nat := [2, 1, 1, 1, 3, 1, 4, 3, 5]
def baseStart_447216 : Nat := 118140960795 + 447216 * 2 ^ 59
def prefixEnd_447216 : Nat := 4983230072969 + 3 ^ 40 * 447216 * 2
def baseEnd_447216 : Nat := 102060784169434444019243

theorem tailTrace_447216 : CollatzResearch.WordTrace tailWord_447216 prefixEnd_447216 102060784169434444019243 := by
  unfold tailWord_447216
  simp only [CollatzResearch.WordTrace]
  refine ⟨8155653773910142628556751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10874205031880190171409001 8155653773910142628556751)
  ·
    refine ⟨12233480660865213942835127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8155653773910142628556751 12233480660865213942835127)
    ·
      refine ⟨18350220991297820914252691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12233480660865213942835127 18350220991297820914252691)
      ·
        refine ⟨27525331486946731371379037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18350220991297820914252691 27525331486946731371379037)
        ·
          refine ⟨10321999307605024264267139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27525331486946731371379037 10321999307605024264267139)
          ·
            refine ⟨15482998961407536396400709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10321999307605024264267139 15482998961407536396400709)
            ·
              refine ⟨2903062305263913074325133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15482998961407536396400709 2903062305263913074325133)
              ·
                refine ⟨1088648364473967402871925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2903062305263913074325133 1088648364473967402871925)
                ·
                  refine ⟨102060784169434444019243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1088648364473967402871925 102060784169434444019243)
                  ·
                    rfl

theorem cell21_447216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_447216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447216 prefixEnd_447216 := by exact prefixLift 447216
  have htrace : WordTrace (prefixWord ++ tailWord_447216) baseStart_447216 baseEnd_447216 := by
    simpa [prefixWord, tailWord_447216, baseEnd_447216] using wordTrace_append hprefix tailTrace_447216
  have hstable : (prefixWord ++ tailWord_447216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447216).length < 2 ^ (prefixWord ++ tailWord_447216).sum := by decide
  have hdescent : baseEnd_447216 < baseStart_447216 := by decide
  rcases family_descends (prefixWord ++ tailWord_447216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447264 : List Nat := [2, 1, 1, 5, 1, 2, 3, 2, 4]
def baseStart_447264 : Nat := 118140960795 + 447264 * 2 ^ 59
def prefixEnd_447264 : Nat := 4983230072969 + 3 ^ 40 * 447264 * 2
def baseEnd_447264 : Nat := 102071738423397027219145

theorem tailTrace_447264 : CollatzResearch.WordTrace tailWord_447264 prefixEnd_447264 102071738423397027219145 := by
  unfold tailWord_447264
  simp only [CollatzResearch.WordTrace]
  refine ⟨8156529125823194727430423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10875372167764259636573897 8156529125823194727430423)
  ·
    refine ⟨12234793688734792091145635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8156529125823194727430423 12234793688734792091145635)
    ·
      refine ⟨18352190533102188136718453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12234793688734792091145635 18352190533102188136718453)
      ·
        refine ⟨1720517862478330137817355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18352190533102188136718453 1720517862478330137817355)
        ·
          refine ⟨2580776793717495206726033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1720517862478330137817355 2580776793717495206726033)
          ·
            refine ⟨1935582595288121405044525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2580776793717495206726033 1935582595288121405044525)
            ·
              refine ⟨725843473233045526891697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1935582595288121405044525 725843473233045526891697)
              ·
                refine ⟨544382604924784145168773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725843473233045526891697 544382604924784145168773)
                ·
                  refine ⟨102071738423397027219145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 544382604924784145168773 102071738423397027219145)
                  ·
                    rfl

theorem cell21_447264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_447264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447264 prefixEnd_447264 := by exact prefixLift 447264
  have htrace : WordTrace (prefixWord ++ tailWord_447264) baseStart_447264 baseEnd_447264 := by
    simpa [prefixWord, tailWord_447264, baseEnd_447264] using wordTrace_append hprefix tailTrace_447264
  have hstable : (prefixWord ++ tailWord_447264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447264).length < 2 ^ (prefixWord ++ tailWord_447264).sum := by decide
  have hdescent : baseEnd_447264 < baseStart_447264 := by decide
  rcases family_descends (prefixWord ++ tailWord_447264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447295 : List Nat := [1, 1, 2, 2, 5, 3, 2, 5]
def baseStart_447295 : Nat := 118140960795 + 447295 * 2 ^ 59
def prefixEnd_447295 : Nat := 4983230072969 + 3 ^ 40 * 447295 * 2
def baseEnd_447295 : Nat := 34026271015249287400805

theorem tailTrace_447295 : CollatzResearch.WordTrace tailWord_447295 prefixEnd_447295 34026271015249287400805 := by
  unfold tailWord_447295
  simp only [CollatzResearch.WordTrace]
  refine ⟨16314188914534081749239339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10876125943022721166159559 16314188914534081749239339)
  ·
    refine ⟨24471283371801122623859009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16314188914534081749239339 24471283371801122623859009)
    ·
      refine ⟨18353462528850841967894257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24471283371801122623859009 18353462528850841967894257)
      ·
        refine ⟨13765096896638131475920693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18353462528850841967894257 13765096896638131475920693)
        ·
          refine ⟨1290477834059824825867565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13765096896638131475920693 1290477834059824825867565)
          ·
            refine ⟨483929187772434309700337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1290477834059824825867565 483929187772434309700337)
            ·
              refine ⟨362946890829325732275253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483929187772434309700337 362946890829325732275253)
              ·
                refine ⟨34026271015249287400805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 362946890829325732275253 34026271015249287400805)
                ·
                  rfl

theorem cell21_447295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 5].length) (baseStart_447295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447295 prefixEnd_447295 := by exact prefixLift 447295
  have htrace : WordTrace (prefixWord ++ tailWord_447295) baseStart_447295 baseEnd_447295 := by
    simpa [prefixWord, tailWord_447295, baseEnd_447295] using wordTrace_append hprefix tailTrace_447295
  have hstable : (prefixWord ++ tailWord_447295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447295).length < 2 ^ (prefixWord ++ tailWord_447295).sum := by decide
  have hdescent : baseEnd_447295 < baseStart_447295 := by decide
  rcases family_descends (prefixWord ++ tailWord_447295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
