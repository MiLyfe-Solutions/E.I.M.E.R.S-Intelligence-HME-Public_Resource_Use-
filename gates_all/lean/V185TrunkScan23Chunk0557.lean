import V185TrunkScan23Chunk0556

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3291994 : List Nat := [3, 1, 1, 2, 1, 4, 3, 1, 7]
def baseStart_3291994 : Nat := 118140960795 + 3291994 * 2 ^ 59
def prefixEnd_3291994 : Nat := 4983230072969 + 3 ^ 40 * 3291994 * 2
def baseEnd_3291994 : Nat := 187819470413033143559489

theorem tailTrace_3291994 : CollatzResearch.WordTrace tailWord_3291994 prefixEnd_3291994 187819470413033143559489 := by
  unfold tailWord_3291994
  simp only [CollatzResearch.WordTrace]
  refine ⟨30017221308918860164766759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80045923490450293772711357 30017221308918860164766759)
  ·
    refine ⟨45025831963378290247150139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30017221308918860164766759 45025831963378290247150139)
    ·
      refine ⟨67538747945067435370725209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45025831963378290247150139 67538747945067435370725209)
      ·
        refine ⟨50654060958800576528043907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67538747945067435370725209 50654060958800576528043907)
        ·
          refine ⟨75981091438200864792065861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50654060958800576528043907 75981091438200864792065861)
          ·
            refine ⟨14246454644662662148512349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75981091438200864792065861 14246454644662662148512349)
            ·
              refine ⟨5342420491748498305692131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14246454644662662148512349 5342420491748498305692131)
              ·
                refine ⟨8013630737622747458538197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5342420491748498305692131 8013630737622747458538197)
                ·
                  refine ⟨187819470413033143559489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8013630737622747458538197 187819470413033143559489)
                  ·
                    rfl

theorem cell23_3291994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 7].length) (baseStart_3291994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3291994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3291994 prefixEnd_3291994 := by exact prefixLift 3291994
  have htrace : WordTrace (prefixWord ++ tailWord_3291994) baseStart_3291994 baseEnd_3291994 := by
    simpa [prefixWord, tailWord_3291994, baseEnd_3291994] using wordTrace_append hprefix tailTrace_3291994
  have hstable : (prefixWord ++ tailWord_3291994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291994).length < 2 ^ (prefixWord ++ tailWord_3291994).sum := by decide
  have hdescent : baseEnd_3291994 < baseStart_3291994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292005 : List Nat := [1, 3, 1, 3, 1, 1, 6, 1, 2, 2, 2]
def baseStart_3292005 : Nat := 118140960795 + 3292005 * 2 ^ 59
def prefixEnd_3292005 : Nat := 4983230072969 + 3 ^ 40 * 3292005 * 2
def baseEnd_3292005 : Nat := 1690380882004497748997851

theorem tailTrace_3292005 : CollatzResearch.WordTrace tailWord_3292005 prefixEnd_3292005 1690380882004497748997851 := by
  unfold tailWord_3292005
  simp only [CollatzResearch.WordTrace]
  refine ⟨120069286438635589537717469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80046190959090393025144979 120069286438635589537717469)
  ·
    refine ⟨45025982414488346076644051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120069286438635589537717469 45025982414488346076644051)
    ·
      refine ⟨67538973621732519114966077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45025982414488346076644051 67538973621732519114966077)
      ·
        refine ⟨25327115108149694668112279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67538973621732519114966077 25327115108149694668112279)
        ·
          refine ⟨37990672662224542002168419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25327115108149694668112279 37990672662224542002168419)
          ·
            refine ⟨56986008993336813003252629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37990672662224542002168419 56986008993336813003252629)
            ·
              refine ⟨2671219171562663109527467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56986008993336813003252629 2671219171562663109527467)
              ·
                refine ⟨4006828757343994664291201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671219171562663109527467 4006828757343994664291201)
                ·
                  refine ⟨3005121568007995998218401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4006828757343994664291201 3005121568007995998218401)
                  ·
                    refine ⟨2253841176005996998663801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3005121568007995998218401 2253841176005996998663801)
                    ·
                      refine ⟨1690380882004497748997851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2253841176005996998663801 1690380882004497748997851)
                      ·
                        rfl

theorem cell23_3292005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_3292005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292005 prefixEnd_3292005 := by exact prefixLift 3292005
  have htrace : WordTrace (prefixWord ++ tailWord_3292005) baseStart_3292005 baseEnd_3292005 := by
    simpa [prefixWord, tailWord_3292005, baseEnd_3292005] using wordTrace_append hprefix tailTrace_3292005
  have hstable : (prefixWord ++ tailWord_3292005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292005).length < 2 ^ (prefixWord ++ tailWord_3292005).sum := by decide
  have hdescent : baseEnd_3292005 < baseStart_3292005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292088 : List Nat := [2, 1, 2, 1, 2, 4, 1, 5, 1, 4]
def baseStart_3292088 : Nat := 118140960795 + 3292088 * 2 ^ 59
def prefixEnd_3292088 : Nat := 4983230072969 + 3 ^ 40 * 3292088 * 2
def baseEnd_3292088 : Nat := 563474500299606974753323

theorem tailTrace_3292088 : CollatzResearch.WordTrace tailWord_3292088 prefixEnd_3292088 563474500299606974753323 := by
  unfold tailWord_3292088
  simp only [CollatzResearch.WordTrace]
  refine ⟨60036156848667447356494459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80048209131556596475325945 60036156848667447356494459)
  ·
    refine ⟨90054235273001171034741689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60036156848667447356494459 90054235273001171034741689)
    ·
      refine ⟨67540676454750878276056267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90054235273001171034741689 67540676454750878276056267)
      ·
        refine ⟨101311014682126317414084401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67540676454750878276056267 101311014682126317414084401)
        ·
          refine ⟨75983261011594738060563301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101311014682126317414084401 75983261011594738060563301)
          ·
            refine ⟨14246861439674013386355619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75983261011594738060563301 14246861439674013386355619)
            ·
              refine ⟨21370292159511020079533429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14246861439674013386355619 21370292159511020079533429)
              ·
                refine ⟨2003464889954158132456259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21370292159511020079533429 2003464889954158132456259)
                ·
                  refine ⟨3005197334931237198684389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2003464889954158132456259 3005197334931237198684389)
                  ·
                    refine ⟨563474500299606974753323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3005197334931237198684389 563474500299606974753323)
                    ·
                      rfl

theorem cell23_3292088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 1, 4].length) (baseStart_3292088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292088 prefixEnd_3292088 := by exact prefixLift 3292088
  have htrace : WordTrace (prefixWord ++ tailWord_3292088) baseStart_3292088 baseEnd_3292088 := by
    simpa [prefixWord, tailWord_3292088, baseEnd_3292088] using wordTrace_append hprefix tailTrace_3292088
  have hstable : (prefixWord ++ tailWord_3292088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292088).length < 2 ^ (prefixWord ++ tailWord_3292088).sum := by decide
  have hdescent : baseEnd_3292088 < baseStart_3292088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292138 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 1, 5, 2]
def baseStart_3292138 : Nat := 118140960795 + 3292138 * 2 ^ 59
def prefixEnd_3292138 : Nat := 4983230072969 + 3 ^ 40 * 3292138 * 2
def baseEnd_3292138 : Nat := 1690449174931545728634739

theorem tailTrace_3292138 : CollatzResearch.WordTrace tailWord_3292138 prefixEnd_3292138 1690449174931545728634739 := by
  unfold tailWord_3292138
  simp only [CollatzResearch.WordTrace]
  refine ⟨30018534336788438313077267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80049424898102502168206045 30018534336788438313077267)
  ·
    refine ⟨45027801505182657469615901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30018534336788438313077267 45027801505182657469615901)
    ·
      refine ⟨16885425564443496551105963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45027801505182657469615901 16885425564443496551105963)
      ·
        refine ⟨25328138346665244826658945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16885425564443496551105963 25328138346665244826658945)
        ·
          refine ⟨18996103759998933619994209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25328138346665244826658945 18996103759998933619994209)
          ·
            refine ⟨14247077819999200214995657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18996103759998933619994209 14247077819999200214995657)
            ·
              refine ⟨10685308364999400161246743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14247077819999200214995657 10685308364999400161246743)
              ·
                refine ⟨16027962547499100241870115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10685308364999400161246743 16027962547499100241870115)
                ·
                  refine ⟨24041943821248650362805173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16027962547499100241870115 24041943821248650362805173)
                  ·
                    refine ⟨2253932233242060971512985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24041943821248650362805173 2253932233242060971512985)
                    ·
                      refine ⟨1690449174931545728634739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2253932233242060971512985 1690449174931545728634739)
                      ·
                        rfl

theorem cell23_3292138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_3292138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292138 prefixEnd_3292138 := by exact prefixLift 3292138
  have htrace : WordTrace (prefixWord ++ tailWord_3292138) baseStart_3292138 baseEnd_3292138 := by
    simpa [prefixWord, tailWord_3292138, baseEnd_3292138] using wordTrace_append hprefix tailTrace_3292138
  have hstable : (prefixWord ++ tailWord_3292138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292138).length < 2 ^ (prefixWord ++ tailWord_3292138).sum := by decide
  have hdescent : baseEnd_3292138 < baseStart_3292138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292144 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 3, 6]
def baseStart_3292144 : Nat := 118140960795 + 3292144 * 2 ^ 59
def prefixEnd_3292144 : Nat := 4983230072969 + 3 ^ 40 * 3292144 * 2
def baseEnd_3292144 : Nat := 563484085271824235053237

theorem tailTrace_3292144 : CollatzResearch.WordTrace tailWord_3292144 prefixEnd_3292144 563484085271824235053237 := by
  unfold tailWord_3292144
  simp only [CollatzResearch.WordTrace]
  refine ⟨60037178092566008138513743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80049570790088010851351657 60037178092566008138513743)
  ·
    refine ⟨90055767138849012207770615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60037178092566008138513743 90055767138849012207770615)
    ·
      refine ⟨135083650708273518311655923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90055767138849012207770615 135083650708273518311655923)
      ·
        refine ⟨202625476062410277467483885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135083650708273518311655923 202625476062410277467483885)
        ·
          refine ⟨75984553523403854050306457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202625476062410277467483885 75984553523403854050306457)
          ·
            refine ⟨56988415142552890537729843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75984553523403854050306457 56988415142552890537729843)
            ·
              refine ⟨85482622713829335806594765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56988415142552890537729843 85482622713829335806594765)
              ·
                refine ⟨32055983517686000927473037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85482622713829335806594765 32055983517686000927473037)
                ·
                  refine ⟨12020993819132250347802389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32055983517686000927473037 12020993819132250347802389)
                  ·
                    refine ⟨563484085271824235053237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12020993819132250347802389 563484085271824235053237)
                    ·
                      rfl

theorem cell23_3292144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 3, 6].length) (baseStart_3292144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292144 prefixEnd_3292144 := by exact prefixLift 3292144
  have htrace : WordTrace (prefixWord ++ tailWord_3292144) baseStart_3292144 baseEnd_3292144 := by
    simpa [prefixWord, tailWord_3292144, baseEnd_3292144] using wordTrace_append hprefix tailTrace_3292144
  have hstable : (prefixWord ++ tailWord_3292144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292144).length < 2 ^ (prefixWord ++ tailWord_3292144).sum := by decide
  have hdescent : baseEnd_3292144 < baseStart_3292144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292171 : List Nat := [1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 5]
def baseStart_3292171 : Nat := 118140960795 + 3292171 * 2 ^ 59
def prefixEnd_3292171 : Nat := 4983230072969 + 3 ^ 40 * 3292171 * 2
def baseEnd_3292171 : Nat := 1690466119793144099522087

theorem tailTrace_3292171 : CollatzResearch.WordTrace tailWord_3292171 prefixEnd_3292171 1690466119793144099522087 := by
  unfold tailWord_3292171
  simp only [CollatzResearch.WordTrace]
  refine ⟨120075340956034199888260367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80050227304022799925506911 120075340956034199888260367)
  ·
    refine ⟨180113011434051299832390551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120075340956034199888260367 180113011434051299832390551)
    ·
      refine ⟨270169517151076949748585827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180113011434051299832390551 270169517151076949748585827)
      ·
        refine ⟨405254275726615424622878741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270169517151076949748585827 405254275726615424622878741)
        ·
          refine ⟨18996294174685098029197441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 405254275726615424622878741 18996294174685098029197441)
          ·
            refine ⟨14247220631013823521898081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18996294174685098029197441 14247220631013823521898081)
            ·
              refine ⟨10685415473260367641423561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14247220631013823521898081 10685415473260367641423561)
              ·
                refine ⟨8014061604945275731067671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10685415473260367641423561 8014061604945275731067671)
                ·
                  refine ⟨12021092407417913596601507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8014061604945275731067671 12021092407417913596601507)
                  ·
                    refine ⟨18031638611126870394902261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12021092407417913596601507 18031638611126870394902261)
                    ·
                      refine ⟨1690466119793144099522087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18031638611126870394902261 1690466119793144099522087)
                      ·
                        rfl

theorem cell23_3292171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 5].length) (baseStart_3292171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292171 prefixEnd_3292171 := by exact prefixLift 3292171
  have htrace : WordTrace (prefixWord ++ tailWord_3292171) baseStart_3292171 baseEnd_3292171 := by
    simpa [prefixWord, tailWord_3292171, baseEnd_3292171] using wordTrace_append hprefix tailTrace_3292171
  have hstable : (prefixWord ++ tailWord_3292171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292171).length < 2 ^ (prefixWord ++ tailWord_3292171).sum := by decide
  have hdescent : baseEnd_3292171 < baseStart_3292171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292181 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_3292181 : Nat := 118140960795 + 3292181 * 2 ^ 59
def prefixEnd_3292181 : Nat := 4983230072969 + 3 ^ 40 * 3292181 * 2
def baseEnd_3292181 : Nat := 1690471254599689060397041

theorem tailTrace_3292181 : CollatzResearch.WordTrace tailWord_3292181 prefixEnd_3292181 1690471254599689060397041 := by
  unfold tailWord_3292181
  simp only [CollatzResearch.WordTrace]
  refine ⟨120075705685997971596124397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80050470457331981064082931 120075705685997971596124397)
  ·
    refine ⟨45028389632249239348546649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120075705685997971596124397 45028389632249239348546649)
    ·
      refine ⟨33771292224186929511409987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45028389632249239348546649 33771292224186929511409987)
      ·
        refine ⟨50656938336280394267114981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33771292224186929511409987 50656938336280394267114981)
        ·
          refine ⟨9498175938052573925084059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50656938336280394267114981 9498175938052573925084059)
          ·
            refine ⟨14247263907078860887626089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9498175938052573925084059 14247263907078860887626089)
            ·
              refine ⟨10685447930309145665719567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14247263907078860887626089 10685447930309145665719567)
              ·
                refine ⟨16028171895463718498579351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10685447930309145665719567 16028171895463718498579351)
                ·
                  refine ⟨24042257843195577747869027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16028171895463718498579351 24042257843195577747869027)
                  ·
                    refine ⟨36063386764793366621803541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24042257843195577747869027 36063386764793366621803541)
                    ·
                      refine ⟨1690471254599689060397041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36063386764793366621803541 1690471254599689060397041)
                      ·
                        rfl

theorem cell23_3292181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_3292181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292181 prefixEnd_3292181 := by exact prefixLift 3292181
  have htrace : WordTrace (prefixWord ++ tailWord_3292181) baseStart_3292181 baseEnd_3292181 := by
    simpa [prefixWord, tailWord_3292181, baseEnd_3292181] using wordTrace_append hprefix tailTrace_3292181
  have hstable : (prefixWord ++ tailWord_3292181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292181).length < 2 ^ (prefixWord ++ tailWord_3292181).sum := by decide
  have hdescent : baseEnd_3292181 < baseStart_3292181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292202 : List Nat := [3, 1, 4, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_3292202 : Nat := 118140960795 + 3292202 * 2 ^ 59
def prefixEnd_3292202 : Nat := 4983230072969 + 3 ^ 40 * 3292202 * 2
def baseEnd_3292202 : Nat := 1690482037693433478234445

theorem tailTrace_3292202 : CollatzResearch.WordTrace tailWord_3292202 prefixEnd_3292202 1690482037693433478234445 := by
  unfold tailWord_3292202
  simp only [CollatzResearch.WordTrace]
  refine ⟨30019117904730473045659715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80050981079281261455092573 30019117904730473045659715)
  ·
    refine ⟨45028676857095709568489573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30019117904730473045659715 45028676857095709568489573)
    ·
      refine ⟨8442876910705445544091795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45028676857095709568489573 8442876910705445544091795)
      ·
        refine ⟨12664315366058168316137693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8442876910705445544091795 12664315366058168316137693)
        ·
          refine ⟨4749118262271813118551635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12664315366058168316137693 4749118262271813118551635)
          ·
            refine ⟨7123677393407719677827453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4749118262271813118551635 7123677393407719677827453)
            ·
              refine ⟨2671379022527894879185295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7123677393407719677827453 2671379022527894879185295)
              ·
                refine ⟨4007068533791842318777943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671379022527894879185295 4007068533791842318777943)
                ·
                  refine ⟨6010602800687763478166915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4007068533791842318777943 6010602800687763478166915)
                  ·
                    refine ⟨9015904201031645217250373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6010602800687763478166915 9015904201031645217250373)
                    ·
                      refine ⟨1690482037693433478234445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9015904201031645217250373 1690482037693433478234445)
                      ·
                        rfl

theorem cell23_3292202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_3292202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292202 prefixEnd_3292202 := by exact prefixLift 3292202
  have htrace : WordTrace (prefixWord ++ tailWord_3292202) baseStart_3292202 baseEnd_3292202 := by
    simpa [prefixWord, tailWord_3292202, baseEnd_3292202] using wordTrace_append hprefix tailTrace_3292202
  have hstable : (prefixWord ++ tailWord_3292202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292202).length < 2 ^ (prefixWord ++ tailWord_3292202).sum := by decide
  have hdescent : baseEnd_3292202 < baseStart_3292202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292212 : List Nat := [2, 5, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_3292212 : Nat := 118140960795 + 3292212 * 2 ^ 59
def prefixEnd_3292212 : Nat := 4983230072969 + 3 ^ 40 * 3292212 * 2
def baseEnd_3292212 : Nat := 563495724166659479703133

theorem tailTrace_3292212 : CollatzResearch.WordTrace tailWord_3292212 prefixEnd_3292212 563495724166659479703133 := by
  unfold tailWord_3292212
  simp only [CollatzResearch.WordTrace]
  refine ⟨60038418174442831945251445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80051224232590442593668593 60038418174442831945251445)
  ·
    refine ⟨5628601703854015494867323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60038418174442831945251445 5628601703854015494867323)
    ·
      refine ⟨8442902555781023242300985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5628601703854015494867323 8442902555781023242300985)
      ·
        refine ⟨6332176916835767431725739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8442902555781023242300985 6332176916835767431725739)
        ·
          refine ⟨9498265375253651147588609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6332176916835767431725739 9498265375253651147588609)
          ·
            refine ⟨7123699031440238360691457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9498265375253651147588609 7123699031440238360691457)
            ·
              refine ⟨5342774273580178770518593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7123699031440238360691457 5342774273580178770518593)
              ·
                refine ⟨4007080705185134077888945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5342774273580178770518593 4007080705185134077888945)
                ·
                  refine ⟨3005310528888850558416709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4007080705185134077888945 3005310528888850558416709)
                  ·
                    refine ⟨563495724166659479703133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3005310528888850558416709 563495724166659479703133)
                    ·
                      rfl

theorem cell23_3292212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_3292212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292212 prefixEnd_3292212 := by exact prefixLift 3292212
  have htrace : WordTrace (prefixWord ++ tailWord_3292212) baseStart_3292212 baseEnd_3292212 := by
    simpa [prefixWord, tailWord_3292212, baseEnd_3292212] using wordTrace_append hprefix tailTrace_3292212
  have hstable : (prefixWord ++ tailWord_3292212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292212).length < 2 ^ (prefixWord ++ tailWord_3292212).sum := by decide
  have hdescent : baseEnd_3292212 < baseStart_3292212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292218 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3]
def baseStart_3292218 : Nat := 118140960795 + 3292218 * 2 ^ 59
def prefixEnd_3292218 : Nat := 4983230072969 + 3 ^ 40 * 3292218 * 2
def baseEnd_3292218 : Nat := 1690490253383905415634371

theorem tailTrace_3292218 : CollatzResearch.WordTrace tailWord_3292218 prefixEnd_3292218 1690490253383905415634371 := by
  unfold tailWord_3292218
  simp only [CollatzResearch.WordTrace]
  refine ⟨30019263796715981728805327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80051370124575951276814205 30019263796715981728805327)
  ·
    refine ⟨45028895695073972593207991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30019263796715981728805327 45028895695073972593207991)
    ·
      refine ⟨67543343542610958889811987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45028895695073972593207991 67543343542610958889811987)
      ·
        refine ⟨101315015313916438334717981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67543343542610958889811987 101315015313916438334717981)
        ·
          refine ⟨37993130742718664375519243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101315015313916438334717981 37993130742718664375519243)
          ·
            refine ⟨56989696114077996563278865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37993130742718664375519243 56989696114077996563278865)
            ·
              refine ⟨42742272085558497422459149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56989696114077996563278865 42742272085558497422459149)
              ·
                refine ⟨16028352032084436533422181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42742272085558497422459149 16028352032084436533422181)
                ·
                  refine ⟨3005316006015831850016659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16028352032084436533422181 3005316006015831850016659)
                  ·
                    refine ⟨4507974009023747775024989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3005316006015831850016659 4507974009023747775024989)
                    ·
                      refine ⟨1690490253383905415634371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4507974009023747775024989 1690490253383905415634371)
                      ·
                        rfl

theorem cell23_3292218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3].length) (baseStart_3292218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292218 prefixEnd_3292218 := by exact prefixLift 3292218
  have htrace : WordTrace (prefixWord ++ tailWord_3292218) baseStart_3292218 baseEnd_3292218 := by
    simpa [prefixWord, tailWord_3292218, baseEnd_3292218] using wordTrace_append hprefix tailTrace_3292218
  have hstable : (prefixWord ++ tailWord_3292218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292218).length < 2 ^ (prefixWord ++ tailWord_3292218).sum := by decide
  have hdescent : baseEnd_3292218 < baseStart_3292218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292221 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 2, 7]
def baseStart_3292221 : Nat := 118140960795 + 3292221 * 2 ^ 59
def prefixEnd_3292221 : Nat := 4983230072969 + 3 ^ 40 * 3292221 * 2
def baseEnd_3292221 : Nat := 563497264608622967965619

theorem tailTrace_3292221 : CollatzResearch.WordTrace tailWord_3292221 prefixEnd_3292221 563497264608622967965619 := by
  unfold tailWord_3292221
  simp only [CollatzResearch.WordTrace]
  refine ⟨120077164605853058427580517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80051443070568705618387011 120077164605853058427580517)
  ·
    refine ⟨22514468363597448455171347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120077164605853058427580517 22514468363597448455171347)
    ·
      refine ⟨33771702545396172682757021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22514468363597448455171347 33771702545396172682757021)
      ·
        refine ⟨12664388454523564756033883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33771702545396172682757021 12664388454523564756033883)
        ·
          refine ⟨18996582681785347134050825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12664388454523564756033883 18996582681785347134050825)
          ·
            refine ⟨14247437011339010350538119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18996582681785347134050825 14247437011339010350538119)
            ·
              refine ⟨21371155517008515525807179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14247437011339010350538119 21371155517008515525807179)
              ·
                refine ⟨32056733275512773288710769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21371155517008515525807179 32056733275512773288710769)
                ·
                  refine ⟨24042549956634579966533077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32056733275512773288710769 24042549956634579966533077)
                  ·
                    refine ⟨563497264608622967965619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24042549956634579966533077 563497264608622967965619)
                    ·
                      rfl

theorem cell23_3292221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_3292221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292221 prefixEnd_3292221 := by exact prefixLift 3292221
  have htrace : WordTrace (prefixWord ++ tailWord_3292221) baseStart_3292221 baseEnd_3292221 := by
    simpa [prefixWord, tailWord_3292221, baseEnd_3292221] using wordTrace_append hprefix tailTrace_3292221
  have hstable : (prefixWord ++ tailWord_3292221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292221).length < 2 ^ (prefixWord ++ tailWord_3292221).sum := by decide
  have hdescent : baseEnd_3292221 < baseStart_3292221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292225 : List Nat := [1, 2, 5, 1, 4, 1, 1, 8]
def baseStart_3292225 : Nat := 118140960795 + 3292225 * 2 ^ 59
def prefixEnd_3292225 : Nat := 4983230072969 + 3 ^ 40 * 3292225 * 2
def baseEnd_3292225 : Nat := 62610883249943958823957

theorem tailTrace_3292225 : CollatzResearch.WordTrace tailWord_3292225 prefixEnd_3292225 62610883249943958823957 := by
  unfold tailWord_3292225
  simp only [CollatzResearch.WordTrace]
  refine ⟨120077310497838567110726129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80051540331892378073817419 120077310497838567110726129)
  ·
    refine ⟨90057982873378925333044597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120077310497838567110726129 90057982873378925333044597)
    ·
      refine ⟨8442935894379274249972931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90057982873378925333044597 8442935894379274249972931)
      ·
        refine ⟨12664403841568911374959397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8442935894379274249972931 12664403841568911374959397)
        ·
          refine ⟨2374575720294170882804887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12664403841568911374959397 2374575720294170882804887)
          ·
            refine ⟨3561863580441256324207331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2374575720294170882804887 3561863580441256324207331)
            ·
              refine ⟨5342795370661884486310997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3561863580441256324207331 5342795370661884486310997)
              ·
                refine ⟨62610883249943958823957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5342795370661884486310997 62610883249943958823957)
                ·
                  rfl

theorem cell23_3292225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 8].length) (baseStart_3292225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292225 prefixEnd_3292225 := by exact prefixLift 3292225
  have htrace : WordTrace (prefixWord ++ tailWord_3292225) baseStart_3292225 baseEnd_3292225 := by
    simpa [prefixWord, tailWord_3292225, baseEnd_3292225] using wordTrace_append hprefix tailTrace_3292225
  have hstable : (prefixWord ++ tailWord_3292225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292225).length < 2 ^ (prefixWord ++ tailWord_3292225).sum := by decide
  have hdescent : baseEnd_3292225 < baseStart_3292225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292245 : List Nat := [1, 3, 2, 2, 1, 2, 2, 4, 1, 3, 2]
def baseStart_3292245 : Nat := 118140960795 + 3292245 * 2 ^ 59
def prefixEnd_3292245 : Nat := 4983230072969 + 3 ^ 40 * 3292245 * 2
def baseEnd_3292245 : Nat := 1690504117361576809996747

theorem tailTrace_3292245 : CollatzResearch.WordTrace tailWord_3292245 prefixEnd_3292245 1690504117361576809996747 := by
  unfold tailWord_3292245
  simp only [CollatzResearch.WordTrace]
  refine ⟨120078039957766110526454189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80052026638510740350969459 120078039957766110526454189)
  ·
    refine ⟨45029264984162291447420321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120078039957766110526454189 45029264984162291447420321)
    ·
      refine ⟨33771948738121718585565241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45029264984162291447420321 33771948738121718585565241)
      ·
        refine ⟨25328961553591288939173931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33771948738121718585565241 25328961553591288939173931)
        ·
          refine ⟨37993442330386933408760897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25328961553591288939173931 37993442330386933408760897)
          ·
            refine ⟨28495081747790200056570673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37993442330386933408760897 28495081747790200056570673)
            ·
              refine ⟨21371311310842650042428005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28495081747790200056570673 21371311310842650042428005)
              ·
                refine ⟨4007120870782996882955251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21371311310842650042428005 4007120870782996882955251)
                ·
                  refine ⟨6010681306174495324432877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4007120870782996882955251 6010681306174495324432877)
                  ·
                    refine ⟨2254005489815435746662329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6010681306174495324432877 2254005489815435746662329)
                    ·
                      refine ⟨1690504117361576809996747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2254005489815435746662329 1690504117361576809996747)
                      ·
                        rfl

theorem cell23_3292245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_3292245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292245 prefixEnd_3292245 := by exact prefixLift 3292245
  have htrace : WordTrace (prefixWord ++ tailWord_3292245) baseStart_3292245 baseEnd_3292245 := by
    simpa [prefixWord, tailWord_3292245, baseEnd_3292245] using wordTrace_append hprefix tailTrace_3292245
  have hstable : (prefixWord ++ tailWord_3292245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292245).length < 2 ^ (prefixWord ++ tailWord_3292245).sum := by decide
  have hdescent : baseEnd_3292245 < baseStart_3292245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292261 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 1, 3, 5]
def baseStart_3292261 : Nat := 118140960795 + 3292261 * 2 ^ 59
def prefixEnd_3292261 : Nat := 4983230072969 + 3 ^ 40 * 3292261 * 2
def baseEnd_3292261 : Nat := 1690512333052048747396673

theorem tailTrace_3292261 : CollatzResearch.WordTrace tailWord_3292261 prefixEnd_3292261 1690512333052048747396673 := by
  unfold tailWord_3292261
  simp only [CollatzResearch.WordTrace]
  refine ⟨120078623525708145259036637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80052415683805430172691091 120078623525708145259036637)
  ·
    refine ⟨45029483822140554472138739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120078623525708145259036637 45029483822140554472138739)
    ·
      refine ⟨67544225733210831708208109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45029483822140554472138739 67544225733210831708208109)
      ·
        refine ⟨25329084649954061890578041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67544225733210831708208109 25329084649954061890578041)
        ·
          refine ⟨18996813487465546417933531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25329084649954061890578041 18996813487465546417933531)
          ·
            refine ⟨28495220231198319626900297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18996813487465546417933531 28495220231198319626900297)
            ·
              refine ⟨21371415173398739720175223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28495220231198319626900297 21371415173398739720175223)
              ·
                refine ⟨32057122760098109580262835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21371415173398739720175223 32057122760098109580262835)
                ·
                  refine ⟨48085684140147164370394253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32057122760098109580262835 48085684140147164370394253)
                  ·
                    refine ⟨18032131552555186638897845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48085684140147164370394253 18032131552555186638897845)
                    ·
                      refine ⟨1690512333052048747396673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18032131552555186638897845 1690512333052048747396673)
                      ·
                        rfl

theorem cell23_3292261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_3292261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292261 prefixEnd_3292261 := by exact prefixLift 3292261
  have htrace : WordTrace (prefixWord ++ tailWord_3292261) baseStart_3292261 baseEnd_3292261 := by
    simpa [prefixWord, tailWord_3292261, baseEnd_3292261] using wordTrace_append hprefix tailTrace_3292261
  have hstable : (prefixWord ++ tailWord_3292261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292261).length < 2 ^ (prefixWord ++ tailWord_3292261).sum := by decide
  have hdescent : baseEnd_3292261 < baseStart_3292261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292271 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 4]
def baseStart_3292271 : Nat := 118140960795 + 3292271 * 2 ^ 59
def prefixEnd_3292271 : Nat := 4983230072969 + 3 ^ 40 * 3292271 * 2
def baseEnd_3292271 : Nat := 1690517467858593708271627

theorem tailTrace_3292271 : CollatzResearch.WordTrace tailWord_3292271 prefixEnd_3292271 1690517467858593708271627 := by
  unfold tailWord_3292271
  simp only [CollatzResearch.WordTrace]
  refine ⟨120078988255671916966900667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80052658837114611311267111 120078988255671916966900667)
  ·
    refine ⟨180118482383507875450351001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120078988255671916966900667 180118482383507875450351001)
    ·
      refine ⟨135088861787630906587763251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180118482383507875450351001 135088861787630906587763251)
      ·
        refine ⟨202633292681446359881644877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135088861787630906587763251 202633292681446359881644877)
        ·
          refine ⟨75987484755542384955616829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202633292681446359881644877 75987484755542384955616829)
          ·
            refine ⟨28495306783328394358356311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75987484755542384955616829 28495306783328394358356311)
            ·
              refine ⟨42742960174992591537534467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28495306783328394358356311 42742960174992591537534467)
              ·
                refine ⟨64114440262488887306301701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42742960174992591537534467 64114440262488887306301701)
                ·
                  refine ⟨12021457549216666369931569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64114440262488887306301701 12021457549216666369931569)
                  ·
                    refine ⟨9016093161912499777448677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12021457549216666369931569 9016093161912499777448677)
                    ·
                      refine ⟨1690517467858593708271627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9016093161912499777448677 1690517467858593708271627)
                      ·
                        rfl

theorem cell23_3292271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_3292271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292271 prefixEnd_3292271 := by exact prefixLift 3292271
  have htrace : WordTrace (prefixWord ++ tailWord_3292271) baseStart_3292271 baseEnd_3292271 := by
    simpa [prefixWord, tailWord_3292271, baseEnd_3292271] using wordTrace_append hprefix tailTrace_3292271
  have hstable : (prefixWord ++ tailWord_3292271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292271).length < 2 ^ (prefixWord ++ tailWord_3292271).sum := by decide
  have hdescent : baseEnd_3292271 < baseStart_3292271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292286 : List Nat := [4, 2, 4, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3292286 : Nat := 118140960795 + 3292286 * 2 ^ 59
def prefixEnd_3292286 : Nat := 4983230072969 + 3 ^ 40 * 3292286 * 2
def baseEnd_3292286 : Nat := 1690525170068411149584059

theorem tailTrace_3292286 : CollatzResearch.WordTrace tailWord_3292286 prefixEnd_3292286 1690525170068411149584059 := by
  unfold tailWord_3292286
  simp only [CollatzResearch.WordTrace]
  refine ⟨15009941918827196816087089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80053023567078383019131141 15009941918827196816087089)
  ·
    refine ⟨11257456439120397612065317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15009941918827196816087089 11257456439120397612065317)
    ·
      refine ⟨2110773082335074552262247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11257456439120397612065317 2110773082335074552262247)
      ·
        refine ⟨3166159623502611828393371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2110773082335074552262247 3166159623502611828393371)
        ·
          refine ⟨4749239435253917742590057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3166159623502611828393371 4749239435253917742590057)
          ·
            refine ⟨3561929576440438306942543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4749239435253917742590057 3561929576440438306942543)
            ·
              refine ⟨5342894364660657460413815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3561929576440438306942543 5342894364660657460413815)
              ·
                refine ⟨8014341546990986190620723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5342894364660657460413815 8014341546990986190620723)
                ·
                  refine ⟨12021512320486479285931085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8014341546990986190620723 12021512320486479285931085)
                  ·
                    refine ⟨4508067120182429732224157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12021512320486479285931085 4508067120182429732224157)
                    ·
                      refine ⟨1690525170068411149584059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4508067120182429732224157 1690525170068411149584059)
                      ·
                        rfl

theorem cell23_3292286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3292286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292286 prefixEnd_3292286 := by exact prefixLift 3292286
  have htrace : WordTrace (prefixWord ++ tailWord_3292286) baseStart_3292286 baseEnd_3292286 := by
    simpa [prefixWord, tailWord_3292286, baseEnd_3292286] using wordTrace_append hprefix tailTrace_3292286
  have hstable : (prefixWord ++ tailWord_3292286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292286).length < 2 ^ (prefixWord ++ tailWord_3292286).sum := by decide
  have hdescent : baseEnd_3292286 < baseStart_3292286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292292 : List Nat := [2, 3, 2, 1, 2, 4, 1, 1, 1, 4, 2]
def baseStart_3292292 : Nat := 118140960795 + 3292292 * 2 ^ 59
def prefixEnd_3292292 : Nat := 4983230072969 + 3 ^ 40 * 3292292 * 2
def baseEnd_3292292 : Nat := 1690528250952338126109031

theorem tailTrace_3292292 : CollatzResearch.WordTrace tailWord_3292292 prefixEnd_3292292 1690528250952338126109031 := by
  unfold tailWord_3292292
  simp only [CollatzResearch.WordTrace]
  refine ⟨60039877094297918776707565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80053169459063891702276753 60039877094297918776707565)
  ·
    refine ⟨22514953910361719541265337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60039877094297918776707565 22514953910361719541265337)
    ·
      refine ⟨16886215432771289655949003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22514953910361719541265337 16886215432771289655949003)
      ·
        refine ⟨25329323149156934483923505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16886215432771289655949003 25329323149156934483923505)
        ·
          refine ⟨18996992361867700862942629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25329323149156934483923505 18996992361867700862942629)
          ·
            refine ⟨3561936067850193911801743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18996992361867700862942629 3561936067850193911801743)
            ·
              refine ⟨5342904101775290867702615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3561936067850193911801743 5342904101775290867702615)
              ·
                refine ⟨8014356152662936301553923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5342904101775290867702615 8014356152662936301553923)
                ·
                  refine ⟨12021534228994404452330885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8014356152662936301553923 12021534228994404452330885)
                  ·
                    refine ⟨2254037667936450834812041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12021534228994404452330885 2254037667936450834812041)
                    ·
                      refine ⟨1690528250952338126109031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2254037667936450834812041 1690528250952338126109031)
                      ·
                        rfl

theorem cell23_3292292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_3292292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292292 prefixEnd_3292292 := by exact prefixLift 3292292
  have htrace : WordTrace (prefixWord ++ tailWord_3292292) baseStart_3292292 baseEnd_3292292 := by
    simpa [prefixWord, tailWord_3292292, baseEnd_3292292] using wordTrace_append hprefix tailTrace_3292292
  have hstable : (prefixWord ++ tailWord_3292292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292292).length < 2 ^ (prefixWord ++ tailWord_3292292).sum := by decide
  have hdescent : baseEnd_3292292 < baseStart_3292292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292338 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_3292338 : Nat := 118140960795 + 3292338 * 2 ^ 59
def prefixEnd_3292338 : Nat := 4983230072969 + 3 ^ 40 * 3292338 * 2
def baseEnd_3292338 : Nat := 1690551871062444946133819

theorem tailTrace_3292338 : CollatzResearch.WordTrace tailWord_3292338 prefixEnd_3292338 1690551871062444946133819 := by
  unfold tailWord_3292338
  simp only [CollatzResearch.WordTrace]
  refine ⟨30020357986607296852397417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80054287964286124939726445 30020357986607296852397417)
  ·
    refine ⟨22515268489955472639298063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30020357986607296852397417 22515268489955472639298063)
    ·
      refine ⟨33772902734933208958947095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22515268489955472639298063 33772902734933208958947095)
      ·
        refine ⟨50659354102399813438420643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33772902734933208958947095 50659354102399813438420643)
        ·
          refine ⟨75989031153599720157630965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50659354102399813438420643 75989031153599720157630965)
          ·
            refine ⟨7123971670649973764777903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75989031153599720157630965 7123971670649973764777903)
            ·
              refine ⟨10685957505974960647166855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7123971670649973764777903 10685957505974960647166855)
              ·
                refine ⟨16028936258962440970750283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10685957505974960647166855 16028936258962440970750283)
                ·
                  refine ⟨24043404388443661456125425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16028936258962440970750283 24043404388443661456125425)
                  ·
                    refine ⟨18032553291332746092094069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24043404388443661456125425 18032553291332746092094069)
                    ·
                      refine ⟨1690551871062444946133819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18032553291332746092094069 1690551871062444946133819)
                      ·
                        rfl

theorem cell23_3292338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_3292338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292338 prefixEnd_3292338 := by exact prefixLift 3292338
  have htrace : WordTrace (prefixWord ++ tailWord_3292338) baseStart_3292338 baseEnd_3292338 := by
    simpa [prefixWord, tailWord_3292338, baseEnd_3292338] using wordTrace_append hprefix tailTrace_3292338
  have hstable : (prefixWord ++ tailWord_3292338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292338).length < 2 ^ (prefixWord ++ tailWord_3292338).sum := by decide
  have hdescent : baseEnd_3292338 < baseStart_3292338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292385 : List Nat := [1, 2, 3, 1, 3, 2, 2, 2, 2, 2, 3]
def baseStart_3292385 : Nat := 118140960795 + 3292385 * 2 ^ 59
def prefixEnd_3292385 : Nat := 4983230072969 + 3 ^ 40 * 3292385 * 2
def baseEnd_3292385 : Nat := 1690576004653206262246103

theorem tailTrace_3292385 : CollatzResearch.WordTrace tailWord_3292385 prefixEnd_3292385 1690576004653206262246103 := by
  unfold tailWord_3292385
  simp only [CollatzResearch.WordTrace]
  refine ⟨120083146177258914436550609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80055430784839276291033739 120083146177258914436550609)
  ·
    refine ⟨90062359632944185827412957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120083146177258914436550609 90062359632944185827412957)
    ·
      refine ⟨33773384862354069685279859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90062359632944185827412957 33773384862354069685279859)
      ·
        refine ⟨50660077293531104527919789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33773384862354069685279859 50660077293531104527919789)
        ·
          refine ⟨18997528985074164197969921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50660077293531104527919789 18997528985074164197969921)
          ·
            refine ⟨14248146738805623148477441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18997528985074164197969921 14248146738805623148477441)
            ·
              refine ⟨10686110054104217361358081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14248146738805623148477441 10686110054104217361358081)
              ·
                refine ⟨8014582540578163021018561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10686110054104217361358081 8014582540578163021018561)
                ·
                  refine ⟨6010936905433622265763921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8014582540578163021018561 6010936905433622265763921)
                  ·
                    refine ⟨4508202679075216699322941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6010936905433622265763921 4508202679075216699322941)
                    ·
                      refine ⟨1690576004653206262246103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4508202679075216699322941 1690576004653206262246103)
                      ·
                        rfl

theorem cell23_3292385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_3292385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292385 prefixEnd_3292385 := by exact prefixLift 3292385
  have htrace : WordTrace (prefixWord ++ tailWord_3292385) baseStart_3292385 baseEnd_3292385 := by
    simpa [prefixWord, tailWord_3292385, baseEnd_3292385] using wordTrace_append hprefix tailTrace_3292385
  have hstable : (prefixWord ++ tailWord_3292385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292385).length < 2 ^ (prefixWord ++ tailWord_3292385).sum := by decide
  have hdescent : baseEnd_3292385 < baseStart_3292385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292388 : List Nat := [2, 3, 1, 1, 1, 2, 3, 4, 6]
def baseStart_3292388 : Nat := 118140960795 + 3292388 * 2 ^ 59
def prefixEnd_3292388 : Nat := 4983230072969 + 3 ^ 40 * 3292388 * 2
def baseEnd_3292388 : Nat := 187841949455018861167621

theorem tailTrace_3292388 : CollatzResearch.WordTrace tailWord_3292388 prefixEnd_3292388 187841949455018861167621 := by
  unfold tailWord_3292388
  simp only [CollatzResearch.WordTrace]
  refine ⟨60041627798124022974454909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80055503730832030632606545 60041627798124022974454909)
  ·
    refine ⟨22515610424296508615420591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60041627798124022974454909 22515610424296508615420591)
    ·
      refine ⟨33773415636444762923130887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22515610424296508615420591 33773415636444762923130887)
      ·
        refine ⟨50660123454667144384696331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33773415636444762923130887 50660123454667144384696331)
        ·
          refine ⟨75990185182000716577044497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50660123454667144384696331 75990185182000716577044497)
          ·
            refine ⟨56992638886500537432783373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75990185182000716577044497 56992638886500537432783373)
            ·
              refine ⟨21372239582437701537293765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56992638886500537432783373 21372239582437701537293765)
              ·
                refine ⟨4007294921707069038242581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21372239582437701537293765 4007294921707069038242581)
                ·
                  refine ⟨187841949455018861167621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4007294921707069038242581 187841949455018861167621)
                  ·
                    rfl

theorem cell23_3292388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_3292388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292388 prefixEnd_3292388 := by exact prefixLift 3292388
  have htrace : WordTrace (prefixWord ++ tailWord_3292388) baseStart_3292388 baseEnd_3292388 := by
    simpa [prefixWord, tailWord_3292388, baseEnd_3292388] using wordTrace_append hprefix tailTrace_3292388
  have hstable : (prefixWord ++ tailWord_3292388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292388).length < 2 ^ (prefixWord ++ tailWord_3292388).sum := by decide
  have hdescent : baseEnd_3292388 < baseStart_3292388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292392 : List Nat := [2, 1, 4, 1, 2, 1, 3, 4, 1, 4]
def baseStart_3292392 : Nat := 118140960795 + 3292392 * 2 ^ 59
def prefixEnd_3292392 : Nat := 4983230072969 + 3 ^ 40 * 3292392 * 2
def baseEnd_3292392 : Nat := 563526533005929244952857

theorem tailTrace_3292392 : CollatzResearch.WordTrace tailWord_3292392 prefixEnd_3292392 563526533005929244952857 := by
  unfold tailWord_3292392
  simp only [CollatzResearch.WordTrace]
  refine ⟨60041700744116777316027715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80055600992155703088036953 60041700744116777316027715)
  ·
    refine ⟨90062551116175165974041573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60041700744116777316027715 90062551116175165974041573)
    ·
      refine ⟨16886728334282843620132795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90062551116175165974041573 16886728334282843620132795)
      ·
        refine ⟨25330092501424265430199193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16886728334282843620132795 25330092501424265430199193)
        ·
          refine ⟨18997569376068199072649395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25330092501424265430199193 18997569376068199072649395)
          ·
            refine ⟨28496354064102298608974093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18997569376068199072649395 28496354064102298608974093)
            ·
              refine ⟨10686132774038361978365285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28496354064102298608974093 10686132774038361978365285)
              ·
                refine ⟨2003649895132192870943491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10686132774038361978365285 2003649895132192870943491)
                ·
                  refine ⟨3005474842698289306415237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2003649895132192870943491 3005474842698289306415237)
                  ·
                    refine ⟨563526533005929244952857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3005474842698289306415237 563526533005929244952857)
                    ·
                      rfl

theorem cell23_3292392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_3292392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292392 prefixEnd_3292392 := by exact prefixLift 3292392
  have htrace : WordTrace (prefixWord ++ tailWord_3292392) baseStart_3292392 baseEnd_3292392 := by
    simpa [prefixWord, tailWord_3292392, baseEnd_3292392] using wordTrace_append hprefix tailTrace_3292392
  have hstable : (prefixWord ++ tailWord_3292392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292392).length < 2 ^ (prefixWord ++ tailWord_3292392).sum := by decide
  have hdescent : baseEnd_3292392 < baseStart_3292392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292415 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 5, 1, 3]
def baseStart_3292415 : Nat := 118140960795 + 3292415 * 2 ^ 59
def prefixEnd_3292415 : Nat := 4983230072969 + 3 ^ 40 * 3292415 * 2
def baseEnd_3292415 : Nat := 1690591409072841144870965

theorem tailTrace_3292415 : CollatzResearch.WordTrace tailWord_3292415 prefixEnd_3292415 1690591409072841144870965 := by
  unfold tailWord_3292415
  simp only [CollatzResearch.WordTrace]
  refine ⟨120084240367150229560142699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80056160244766819706761799 120084240367150229560142699)
  ·
    refine ⟨180126360550725344340214049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120084240367150229560142699 180126360550725344340214049)
    ·
      refine ⟨135094770413044008255160537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180126360550725344340214049 135094770413044008255160537)
      ·
        refine ⟨101321077809783006191370403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135094770413044008255160537 101321077809783006191370403)
        ·
          refine ⟨151981616714674509287055605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101321077809783006191370403 151981616714674509287055605)
          ·
            refine ⟨14248276567000735245661463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151981616714674509287055605 14248276567000735245661463)
            ·
              refine ⟨21372414850501102868492195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14248276567000735245661463 21372414850501102868492195)
              ·
                refine ⟨32058622275751654302738293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21372414850501102868492195 32058622275751654302738293)
                ·
                  refine ⟨3005495838351717590881715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32058622275751654302738293 3005495838351717590881715)
                  ·
                    refine ⟨4508243757527576386322573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3005495838351717590881715 4508243757527576386322573)
                    ·
                      refine ⟨1690591409072841144870965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4508243757527576386322573 1690591409072841144870965)
                      ·
                        rfl

theorem cell23_3292415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 1, 3].length) (baseStart_3292415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292415 prefixEnd_3292415 := by exact prefixLift 3292415
  have htrace : WordTrace (prefixWord ++ tailWord_3292415) baseStart_3292415 baseEnd_3292415 := by
    simpa [prefixWord, tailWord_3292415, baseEnd_3292415] using wordTrace_append hprefix tailTrace_3292415
  have hstable : (prefixWord ++ tailWord_3292415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292415).length < 2 ^ (prefixWord ++ tailWord_3292415).sum := by decide
  have hdescent : baseEnd_3292415 < baseStart_3292415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292425 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 1, 5, 2]
def baseStart_3292425 : Nat := 118140960795 + 3292425 * 2 ^ 59
def prefixEnd_3292425 : Nat := 4983230072969 + 3 ^ 40 * 3292425 * 2
def baseEnd_3292425 : Nat := 1690596543879386105745919

theorem tailTrace_3292425 : CollatzResearch.WordTrace tailWord_3292425 prefixEnd_3292425 1690596543879386105745919 := by
  unfold tailWord_3292425
  simp only [CollatzResearch.WordTrace]
  refine ⟨120084605097114001268006729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80056403398076000845337819 120084605097114001268006729)
  ·
    refine ⟨90063453822835500951005047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120084605097114001268006729 90063453822835500951005047)
    ·
      refine ⟨135095180734253251426507571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90063453822835500951005047 135095180734253251426507571)
      ·
        refine ⟨202642771101379877139761357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135095180734253251426507571 202642771101379877139761357)
        ·
          refine ⟨75991039163017453927410509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202642771101379877139761357 75991039163017453927410509)
          ·
            refine ⟨28496639686131545222778941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75991039163017453927410509 28496639686131545222778941)
            ·
              refine ⟨10686239882299329458542103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28496639686131545222778941 10686239882299329458542103)
              ·
                refine ⟨16029359823448994187813155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10686239882299329458542103 16029359823448994187813155)
                ·
                  refine ⟨24044039735173491281719733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16029359823448994187813155 24044039735173491281719733)
                  ·
                    refine ⟨2254128725172514807661225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24044039735173491281719733 2254128725172514807661225)
                    ·
                      refine ⟨1690596543879386105745919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2254128725172514807661225 1690596543879386105745919)
                      ·
                        rfl

theorem cell23_3292425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 5, 2].length) (baseStart_3292425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292425 prefixEnd_3292425 := by exact prefixLift 3292425
  have htrace : WordTrace (prefixWord ++ tailWord_3292425) baseStart_3292425 baseEnd_3292425 := by
    simpa [prefixWord, tailWord_3292425, baseEnd_3292425] using wordTrace_append hprefix tailTrace_3292425
  have hstable : (prefixWord ++ tailWord_3292425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292425).length < 2 ^ (prefixWord ++ tailWord_3292425).sum := by decide
  have hdescent : baseEnd_3292425 < baseStart_3292425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292465 : List Nat := [1, 2, 2, 3, 3, 1, 3, 1, 1, 6]
def baseStart_3292465 : Nat := 118140960795 + 3292465 * 2 ^ 59
def prefixEnd_3292465 : Nat := 4983230072969 + 3 ^ 40 * 3292465 * 2
def baseEnd_3292465 : Nat := 563539027701855316415245

theorem tailTrace_3292465 : CollatzResearch.WordTrace tailWord_3292465 prefixEnd_3292465 563539027701855316415245 := by
  unfold tailWord_3292465
  simp only [CollatzResearch.WordTrace]
  refine ⟨120086064016969088099462849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80057376011312725399641899 120086064016969088099462849)
  ·
    refine ⟨90064548012726816074597137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120086064016969088099462849 90064548012726816074597137)
    ·
      refine ⟨67548411009545112055947853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90064548012726816074597137 67548411009545112055947853)
      ·
        refine ⟨25330654128579417020980445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67548411009545112055947853 25330654128579417020980445)
        ·
          refine ⟨9498995298217281382867667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25330654128579417020980445 9498995298217281382867667)
          ·
            refine ⟨14248492947325922074301501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9498995298217281382867667 14248492947325922074301501)
            ·
              refine ⟨5343184855247220777863063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14248492947325922074301501 5343184855247220777863063)
              ·
                refine ⟨8014777282870831166794595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5343184855247220777863063 8014777282870831166794595)
                ·
                  refine ⟨12022165924306246750191893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8014777282870831166794595 12022165924306246750191893)
                  ·
                    refine ⟨563539027701855316415245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12022165924306246750191893 563539027701855316415245)
                    ·
                      rfl

theorem cell23_3292465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_3292465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292465 prefixEnd_3292465 := by exact prefixLift 3292465
  have htrace : WordTrace (prefixWord ++ tailWord_3292465) baseStart_3292465 baseEnd_3292465 := by
    simpa [prefixWord, tailWord_3292465, baseEnd_3292465] using wordTrace_append hprefix tailTrace_3292465
  have hstable : (prefixWord ++ tailWord_3292465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292465).length < 2 ^ (prefixWord ++ tailWord_3292465).sum := by decide
  have hdescent : baseEnd_3292465 < baseStart_3292465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292492 : List Nat := [2, 2, 1, 3, 2, 2, 2, 3, 1, 2, 3]
def baseStart_3292492 : Nat := 118140960795 + 3292492 * 2 ^ 59
def prefixEnd_3292492 : Nat := 4983230072969 + 3 ^ 40 * 3292492 * 2
def baseEnd_3292492 : Nat := 1690630947083237343608111

theorem tailTrace_3292492 : CollatzResearch.WordTrace tailWord_3292492 prefixEnd_3292492 1690630947083237343608111 := by
  unfold tailWord_3292492
  simp only [CollatzResearch.WordTrace]
  refine ⟨60043524393935635855347865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80058032525247514473797153 60043524393935635855347865)
  ·
    refine ⟨45032643295451726891510899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60043524393935635855347865 45032643295451726891510899)
    ·
      refine ⟨67548964943177590337266349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45032643295451726891510899 67548964943177590337266349)
      ·
        refine ⟨25330861853691596376474881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67548964943177590337266349 25330861853691596376474881)
        ·
          refine ⟨18998146390268697282356161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25330861853691596376474881 18998146390268697282356161)
          ·
            refine ⟨14248609792701522961767121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18998146390268697282356161 14248609792701522961767121)
            ·
              refine ⟨10686457344526142221325341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14248609792701522961767121 10686457344526142221325341)
              ·
                refine ⟨4007421504197303332997003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10686457344526142221325341 4007421504197303332997003)
                ·
                  refine ⟨6011132256295954999495505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4007421504197303332997003 6011132256295954999495505)
                  ·
                    refine ⟨4508349192221966249621629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6011132256295954999495505 4508349192221966249621629)
                    ·
                      refine ⟨1690630947083237343608111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4508349192221966249621629 1690630947083237343608111)
                      ·
                        rfl

theorem cell23_3292492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_3292492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292492 prefixEnd_3292492 := by exact prefixLift 3292492
  have htrace : WordTrace (prefixWord ++ tailWord_3292492) baseStart_3292492 baseEnd_3292492 := by
    simpa [prefixWord, tailWord_3292492, baseEnd_3292492] using wordTrace_append hprefix tailTrace_3292492
  have hstable : (prefixWord ++ tailWord_3292492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292492).length < 2 ^ (prefixWord ++ tailWord_3292492).sum := by decide
  have hdescent : baseEnd_3292492 < baseStart_3292492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292538 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 1, 8]
def baseStart_3292538 : Nat := 118140960795 + 3292538 * 2 ^ 59
def prefixEnd_3292538 : Nat := 4983230072969 + 3 ^ 40 * 3292538 * 2
def baseEnd_3292538 : Nat := 563551522397781387877633

theorem tailTrace_3292538 : CollatzResearch.WordTrace tailWord_3292538 prefixEnd_3292538 563551522397781387877633 := by
  unfold tailWord_3292538
  simp only [CollatzResearch.WordTrace]
  refine ⟨30022181636426155391717567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80059151030469747711246845 30022181636426155391717567)
  ·
    refine ⟨45033272454639233087576351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30022181636426155391717567 45033272454639233087576351)
    ·
      refine ⟨67549908681958849631364527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45033272454639233087576351 67549908681958849631364527)
      ·
        refine ⟨101324863022938274447046791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67549908681958849631364527 101324863022938274447046791)
        ·
          refine ⟨151987294534407411670570187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101324863022938274447046791 151987294534407411670570187)
          ·
            refine ⟨227980941801611117505855281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151987294534407411670570187 227980941801611117505855281)
            ·
              refine ⟨170985706351208338129391461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227980941801611117505855281 170985706351208338129391461)
              ·
                refine ⟨32059819940851563399260899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170985706351208338129391461 32059819940851563399260899)
                ·
                  refine ⟨48089729911277345098891349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32059819940851563399260899 48089729911277345098891349)
                  ·
                    refine ⟨563551522397781387877633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48089729911277345098891349 563551522397781387877633)
                    ·
                      rfl

theorem cell23_3292538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_3292538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292538 prefixEnd_3292538 := by exact prefixLift 3292538
  have htrace : WordTrace (prefixWord ++ tailWord_3292538) baseStart_3292538 baseEnd_3292538 := by
    simpa [prefixWord, tailWord_3292538, baseEnd_3292538] using wordTrace_append hprefix tailTrace_3292538
  have hstable : (prefixWord ++ tailWord_3292538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292538).length < 2 ^ (prefixWord ++ tailWord_3292538).sum := by decide
  have hdescent : baseEnd_3292538 < baseStart_3292538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292565 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 2, 4, 3]
def baseStart_3292565 : Nat := 118140960795 + 3292565 * 2 ^ 59
def prefixEnd_3292565 : Nat := 4983230072969 + 3 ^ 40 * 3292565 * 2
def baseEnd_3292565 : Nat := 1690668431171015557995275

theorem tailTrace_3292565 : CollatzResearch.WordTrace tailWord_3292565 prefixEnd_3292565 1690668431171015557995275 := by
  unfold tailWord_3292565
  simp only [CollatzResearch.WordTrace]
  refine ⟨120089711316606805178103149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80059807544404536785402099 120089711316606805178103149)
  ·
    refine ⟨45033641743727551941788681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120089711316606805178103149 45033641743727551941788681)
    ·
      refine ⟨33775231307795663956341511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45033641743727551941788681 33775231307795663956341511)
      ·
        refine ⟨50662846961693495934512267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33775231307795663956341511 50662846961693495934512267)
        ·
          refine ⟨75994270442540243901768401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50662846961693495934512267 75994270442540243901768401)
          ·
            refine ⟨56995702831905182926326301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75994270442540243901768401 56995702831905182926326301)
            ·
              refine ⟨21373388561964443597372363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56995702831905182926326301 21373388561964443597372363)
              ·
                refine ⟨32060082842946665396058545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21373388561964443597372363 32060082842946665396058545)
                ·
                  refine ⟨24045062132209999047043909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32060082842946665396058545 24045062132209999047043909)
                  ·
                    refine ⟨4508449149789374821320733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24045062132209999047043909 4508449149789374821320733)
                    ·
                      refine ⟨1690668431171015557995275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4508449149789374821320733 1690668431171015557995275)
                      ·
                        rfl

theorem cell23_3292565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_3292565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292565 prefixEnd_3292565 := by exact prefixLift 3292565
  have htrace : WordTrace (prefixWord ++ tailWord_3292565) baseStart_3292565 baseEnd_3292565 := by
    simpa [prefixWord, tailWord_3292565, baseEnd_3292565] using wordTrace_append hprefix tailTrace_3292565
  have hstable : (prefixWord ++ tailWord_3292565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292565).length < 2 ^ (prefixWord ++ tailWord_3292565).sum := by decide
  have hdescent : baseEnd_3292565 < baseStart_3292565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292575 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 4]
def baseStart_3292575 : Nat := 118140960795 + 3292575 * 2 ^ 59
def prefixEnd_3292575 : Nat := 4983230072969 + 3 ^ 40 * 3292575 * 2
def baseEnd_3292575 : Nat := 1690673565977560518870229

theorem tailTrace_3292575 : CollatzResearch.WordTrace tailWord_3292575 prefixEnd_3292575 1690673565977560518870229 := by
  unfold tailWord_3292575
  simp only [CollatzResearch.WordTrace]
  refine ⟨120090076046570576885967179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80060050697713717923978119 120090076046570576885967179)
  ·
    refine ⟨180135114069855865328950769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120090076046570576885967179 180135114069855865328950769)
    ·
      refine ⟨135101335552391898996713077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180135114069855865328950769 135101335552391898996713077)
      ·
        refine ⟨12665750208036740530941851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135101335552391898996713077 12665750208036740530941851)
        ·
          refine ⟨18998625312055110796412777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12665750208036740530941851 18998625312055110796412777)
          ·
            refine ⟨14248968984041333097309583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18998625312055110796412777 14248968984041333097309583)
            ·
              refine ⟨21373453476061999645964375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14248968984041333097309583 21373453476061999645964375)
              ·
                refine ⟨32060180214092999468946563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21373453476061999645964375 32060180214092999468946563)
                ·
                  refine ⟨48090270321139499203419845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32060180214092999468946563 48090270321139499203419845)
                  ·
                    refine ⟨9016925685213656100641221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48090270321139499203419845 9016925685213656100641221)
                    ·
                      refine ⟨1690673565977560518870229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9016925685213656100641221 1690673565977560518870229)
                      ·
                        rfl

theorem cell23_3292575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_3292575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292575 prefixEnd_3292575 := by exact prefixLift 3292575
  have htrace : WordTrace (prefixWord ++ tailWord_3292575) baseStart_3292575 baseEnd_3292575 := by
    simpa [prefixWord, tailWord_3292575, baseEnd_3292575] using wordTrace_append hprefix tailTrace_3292575
  have hstable : (prefixWord ++ tailWord_3292575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292575).length < 2 ^ (prefixWord ++ tailWord_3292575).sum := by decide
  have hdescent : baseEnd_3292575 < baseStart_3292575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292579 : List Nat := [1, 1, 1, 4, 1, 3, 1, 5, 2, 2, 2]
def baseStart_3292579 : Nat := 118140960795 + 3292579 * 2 ^ 59
def prefixEnd_3292579 : Nat := 4983230072969 + 3 ^ 40 * 3292579 * 2
def baseEnd_3292579 : Nat := 1690675619900178503220211

theorem tailTrace_3292579 : CollatzResearch.WordTrace tailWord_3292579 prefixEnd_3292579 1690675619900178503220211 := by
  unfold tailWord_3292579
  simp only [CollatzResearch.WordTrace]
  refine ⟨120090221938556085569112791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80060147959037390379408527 120090221938556085569112791)
  ·
    refine ⟨180135332907834128353669187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120090221938556085569112791 180135332907834128353669187)
    ·
      refine ⟨270202999361751192530503781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180135332907834128353669187 270202999361751192530503781)
      ·
        refine ⟨50663062380328348599469459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270202999361751192530503781 50663062380328348599469459)
        ·
          refine ⟨75994593570492522899204189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50663062380328348599469459 75994593570492522899204189)
          ·
            refine ⟨28497972588934696087201571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75994593570492522899204189 28497972588934696087201571)
            ·
              refine ⟨42746958883402044130802357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28497972588934696087201571 42746958883402044130802357)
              ·
                refine ⟨4007527395318941637262721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42746958883402044130802357 4007527395318941637262721)
                ·
                  refine ⟨3005645546489206227947041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4007527395318941637262721 3005645546489206227947041)
                  ·
                    refine ⟨2254234159866904670960281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3005645546489206227947041 2254234159866904670960281)
                    ·
                      refine ⟨1690675619900178503220211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2254234159866904670960281 1690675619900178503220211)
                      ·
                        rfl

theorem cell23_3292579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_3292579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292579 prefixEnd_3292579 := by exact prefixLift 3292579
  have htrace : WordTrace (prefixWord ++ tailWord_3292579) baseStart_3292579 baseEnd_3292579 := by
    simpa [prefixWord, tailWord_3292579, baseEnd_3292579] using wordTrace_append hprefix tailTrace_3292579
  have hstable : (prefixWord ++ tailWord_3292579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292579).length < 2 ^ (prefixWord ++ tailWord_3292579).sum := by decide
  have hdescent : baseEnd_3292579 < baseStart_3292579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292615 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 4, 5]
def baseStart_3292615 : Nat := 118140960795 + 3292615 * 2 ^ 59
def prefixEnd_3292615 : Nat := 4983230072969 + 3 ^ 40 * 3292615 * 2
def baseEnd_3292615 : Nat := 563564701734580120790015

theorem tailTrace_3292615 : CollatzResearch.WordTrace tailWord_3292615 prefixEnd_3292615 563564701734580120790015 := by
  unfold tailWord_3292615
  simp only [CollatzResearch.WordTrace]
  refine ⟨120091534966425663717423299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80061023310950442478282199 120091534966425663717423299)
  ·
    refine ⟨180137302449638495576134949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120091534966425663717423299 180137302449638495576134949)
    ·
      refine ⟨33775744209307217920525303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180137302449638495576134949 33775744209307217920525303)
      ·
        refine ⟨50663616313960826880787955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33775744209307217920525303 50663616313960826880787955)
        ·
          refine ⟨75995424470941240321181933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50663616313960826880787955 75995424470941240321181933)
          ·
            refine ⟨28498284176602965120443225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75995424470941240321181933 28498284176602965120443225)
            ·
              refine ⟨21373713132452223840332419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28498284176602965120443225 21373713132452223840332419)
              ·
                refine ⟨32060569698678335760498629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21373713132452223840332419 32060569698678335760498629)
                ·
                  refine ⟨6011356818502187955093493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32060569698678335760498629 6011356818502187955093493)
                  ·
                    refine ⟨563564701734580120790015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6011356818502187955093493 563564701734580120790015)
                    ·
                      rfl

theorem cell23_3292615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_3292615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292615 prefixEnd_3292615 := by exact prefixLift 3292615
  have htrace : WordTrace (prefixWord ++ tailWord_3292615) baseStart_3292615 baseEnd_3292615 := by
    simpa [prefixWord, tailWord_3292615, baseEnd_3292615] using wordTrace_append hprefix tailTrace_3292615
  have hstable : (prefixWord ++ tailWord_3292615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292615).length < 2 ^ (prefixWord ++ tailWord_3292615).sum := by decide
  have hdescent : baseEnd_3292615 < baseStart_3292615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292622 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2]
def baseStart_3292622 : Nat := 118140960795 + 3292622 * 2 ^ 59
def prefixEnd_3292622 : Nat := 4983230072969 + 3 ^ 40 * 3292622 * 2
def baseEnd_3292622 : Nat := 1690697699568321834982513

theorem tailTrace_3292622 : CollatzResearch.WordTrace tailWord_3292622 prefixEnd_3292622 1690697699568321834982513 := by
  unfold tailWord_3292622
  simp only [CollatzResearch.WordTrace]
  refine ⟨15011473784675037989116015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80061193518266869275285413 15011473784675037989116015)
  ·
    refine ⟨22517210677012556983674023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15011473784675037989116015 22517210677012556983674023)
    ·
      refine ⟨33775816015518835475511035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22517210677012556983674023 33775816015518835475511035)
      ·
        refine ⟨50663724023278253213266553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33775816015518835475511035 50663724023278253213266553)
        ·
          refine ⟨37997793017458689909949915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50663724023278253213266553 37997793017458689909949915)
          ·
            refine ⟨56996689526188034864924873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37997793017458689909949915 56996689526188034864924873)
            ·
              refine ⟨42747517144641026148693655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56996689526188034864924873 42747517144641026148693655)
              ·
                refine ⟨64121275716961539223040483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42747517144641026148693655 64121275716961539223040483)
                ·
                  refine ⟨96181913575442308834560725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64121275716961539223040483 96181913575442308834560725)
                  ·
                    refine ⟨2254263599424429113310017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 96181913575442308834560725 2254263599424429113310017)
                    ·
                      refine ⟨1690697699568321834982513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2254263599424429113310017 1690697699568321834982513)
                      ·
                        rfl

theorem cell23_3292622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_3292622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292622 prefixEnd_3292622 := by exact prefixLift 3292622
  have htrace : WordTrace (prefixWord ++ tailWord_3292622) baseStart_3292622 baseEnd_3292622 := by
    simpa [prefixWord, tailWord_3292622, baseEnd_3292622] using wordTrace_append hprefix tailTrace_3292622
  have hstable : (prefixWord ++ tailWord_3292622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292622).length < 2 ^ (prefixWord ++ tailWord_3292622).sum := by decide
  have hdescent : baseEnd_3292622 < baseStart_3292622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292630 : List Nat := [5, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_3292630 : Nat := 118140960795 + 3292630 * 2 ^ 59
def prefixEnd_3292630 : Nat := 4983230072969 + 3 ^ 40 * 3292630 * 2
def baseEnd_3292630 : Nat := 1690701807413557803682477

theorem tailTrace_3292630 : CollatzResearch.WordTrace tailWord_3292630 prefixEnd_3292630 1690701807413557803682477 := by
  unfold tailWord_3292630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7505755128835707579951209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80061388040914214186146229 7505755128835707579951209)
  ·
    refine ⟨5629316346626780684963407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7505755128835707579951209 5629316346626780684963407)
    ·
      refine ⟨8443974519940171027445111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5629316346626780684963407 8443974519940171027445111)
      ·
        refine ⟨12665961779910256541167667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8443974519940171027445111 12665961779910256541167667)
        ·
          refine ⟨18998942669865384811751501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12665961779910256541167667 18998942669865384811751501)
          ·
            refine ⟨7124603501199519304406813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18998942669865384811751501 7124603501199519304406813)
            ·
              refine ⟨2671726312949819739152555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7124603501199519304406813 2671726312949819739152555)
              ·
                refine ⟨4007589469424729608728833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671726312949819739152555 4007589469424729608728833)
                ·
                  refine ⟨3005692102068547206546625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4007589469424729608728833 3005692102068547206546625)
                  ·
                    refine ⟨2254269076551410404909969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3005692102068547206546625 2254269076551410404909969)
                    ·
                      refine ⟨1690701807413557803682477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2254269076551410404909969 1690701807413557803682477)
                      ·
                        rfl

theorem cell23_3292630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_3292630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292630 prefixEnd_3292630 := by exact prefixLift 3292630
  have htrace : WordTrace (prefixWord ++ tailWord_3292630) baseStart_3292630 baseEnd_3292630 := by
    simpa [prefixWord, tailWord_3292630, baseEnd_3292630] using wordTrace_append hprefix tailTrace_3292630
  have hstable : (prefixWord ++ tailWord_3292630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292630).length < 2 ^ (prefixWord ++ tailWord_3292630).sum := by decide
  have hdescent : baseEnd_3292630 < baseStart_3292630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292652 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 4, 4, 2]
def baseStart_3292652 : Nat := 118140960795 + 3292652 * 2 ^ 59
def prefixEnd_3292652 : Nat := 4983230072969 + 3 ^ 40 * 3292652 * 2
def baseEnd_3292652 : Nat := 1690713103987956717607375

theorem tailTrace_3292652 : CollatzResearch.WordTrace tailWord_3292652 prefixEnd_3292652 1690713103987956717607375 := by
  unfold tailWord_3292652
  simp only [CollatzResearch.WordTrace]
  refine ⟨60046442233645809518260105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80061922978194412691013473 60046442233645809518260105)
  ·
    refine ⟨45034831675234357138695079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60046442233645809518260105 45034831675234357138695079)
    ·
      refine ⟨67552247512851535708042619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45034831675234357138695079 67552247512851535708042619)
      ·
        refine ⟨101328371269277303562063929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67552247512851535708042619 101328371269277303562063929)
        ·
          refine ⟨75996278451957977671547947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101328371269277303562063929 75996278451957977671547947)
          ·
            refine ⟨113994417677936966507321921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75996278451957977671547947 113994417677936966507321921)
            ·
              refine ⟨85495813258452724880491441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113994417677936966507321921 85495813258452724880491441)
              ·
                refine ⟨64121859943839543660368581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85495813258452724880491441 64121859943839543660368581)
                ·
                  refine ⟨12022848739469914436319109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64121859943839543660368581 12022848739469914436319109)
                  ·
                    refine ⟨2254284138650608956809833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12022848739469914436319109 2254284138650608956809833)
                    ·
                      refine ⟨1690713103987956717607375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2254284138650608956809833 1690713103987956717607375)
                      ·
                        rfl

theorem cell23_3292652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 4, 2].length) (baseStart_3292652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292652 prefixEnd_3292652 := by exact prefixLift 3292652
  have htrace : WordTrace (prefixWord ++ tailWord_3292652) baseStart_3292652 baseEnd_3292652 := by
    simpa [prefixWord, tailWord_3292652, baseEnd_3292652] using wordTrace_append hprefix tailTrace_3292652
  have hstable : (prefixWord ++ tailWord_3292652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292652).length < 2 ^ (prefixWord ++ tailWord_3292652).sum := by decide
  have hdescent : baseEnd_3292652 < baseStart_3292652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292653 : List Nat := [1, 5, 1, 3, 3, 1, 1, 3, 5]
def baseStart_3292653 : Nat := 118140960795 + 3292653 * 2 ^ 59
def prefixEnd_3292653 : Nat := 4983230072969 + 3 ^ 40 * 3292653 * 2
def baseEnd_3292653 : Nat := 187857068607623468188319

theorem tailTrace_3292653 : CollatzResearch.WordTrace tailWord_3292653 prefixEnd_3292653 187857068607623468188319 := by
  unfold tailWord_3292653
  simp only [CollatzResearch.WordTrace]
  refine ⟨120092920940287996207306613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80061947293525330804871075 120092920940287996207306613)
  ·
    refine ⟨11258711338151999644434995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120092920940287996207306613 11258711338151999644434995)
    ·
      refine ⟨16888067007227999466652493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11258711338151999644434995 16888067007227999466652493)
      ·
        refine ⟨6333025127710499799994685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16888067007227999466652493 6333025127710499799994685)
        ·
          refine ⟨2374884422891437424998007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6333025127710499799994685 2374884422891437424998007)
          ·
            refine ⟨3562326634337156137497011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2374884422891437424998007 3562326634337156137497011)
            ·
              refine ⟨5343489951505734206245517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3562326634337156137497011 5343489951505734206245517)
              ·
                refine ⟨2003808731814650327342069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5343489951505734206245517 2003808731814650327342069)
                ·
                  refine ⟨187857068607623468188319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2003808731814650327342069 187857068607623468188319)
                  ·
                    rfl

theorem cell23_3292653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_3292653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292653 prefixEnd_3292653 := by exact prefixLift 3292653
  have htrace : WordTrace (prefixWord ++ tailWord_3292653) baseStart_3292653 baseEnd_3292653 := by
    simpa [prefixWord, tailWord_3292653, baseEnd_3292653] using wordTrace_append hprefix tailTrace_3292653
  have hstable : (prefixWord ++ tailWord_3292653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292653).length < 2 ^ (prefixWord ++ tailWord_3292653).sum := by decide
  have hdescent : baseEnd_3292653 < baseStart_3292653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292679 : List Nat := [1, 1, 4, 3, 2, 1, 3, 1, 3, 4]
def baseStart_3292679 : Nat := 118140960795 + 3292679 * 2 ^ 59
def prefixEnd_3292679 : Nat := 4983230072969 + 3 ^ 40 * 3292679 * 2
def baseEnd_3292679 : Nat := 563575655988542703989917

theorem tailTrace_3292679 : CollatzResearch.WordTrace tailWord_3292679 prefixEnd_3292679 563575655988542703989917 := by
  unfold tailWord_3292679
  simp only [CollatzResearch.WordTrace]
  refine ⟨120093869238193802647753091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80062579492129201765168727 120093869238193802647753091)
  ·
    refine ⟨180140803857290703971629637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120093869238193802647753091 180140803857290703971629637)
    ·
      refine ⟨33776400723242006994680557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180140803857290703971629637 33776400723242006994680557)
      ·
        refine ⟨12666150271215752623005209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33776400723242006994680557 12666150271215752623005209)
        ·
          refine ⟨9499612703411814467253907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12666150271215752623005209 9499612703411814467253907)
          ·
            refine ⟨14249419055117721700880861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9499612703411814467253907 14249419055117721700880861)
            ·
              refine ⟨5343532145669145637830323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14249419055117721700880861 5343532145669145637830323)
              ·
                refine ⟨8015298218503718456745485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5343532145669145637830323 8015298218503718456745485)
                ·
                  refine ⟨3005736831938894421279557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8015298218503718456745485 3005736831938894421279557)
                  ·
                    refine ⟨563575655988542703989917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3005736831938894421279557 563575655988542703989917)
                    ·
                      rfl

theorem cell23_3292679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_3292679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292679 prefixEnd_3292679 := by exact prefixLift 3292679
  have htrace : WordTrace (prefixWord ++ tailWord_3292679) baseStart_3292679 baseEnd_3292679 := by
    simpa [prefixWord, tailWord_3292679, baseEnd_3292679] using wordTrace_append hprefix tailTrace_3292679
  have hstable : (prefixWord ++ tailWord_3292679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292679).length < 2 ^ (prefixWord ++ tailWord_3292679).sum := by decide
  have hdescent : baseEnd_3292679 < baseStart_3292679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292726 : List Nat := [5, 1, 2, 1, 3, 1, 2, 2, 6]
def baseStart_3292726 : Nat := 118140960795 + 3292726 * 2 ^ 59
def prefixEnd_3292726 : Nat := 4983230072969 + 3 ^ 40 * 3292726 * 2
def baseEnd_3292726 : Nat := 187861233506265492009115

theorem tailTrace_3292726 : CollatzResearch.WordTrace tailWord_3292726 prefixEnd_3292726 187861233506265492009115 := by
  unfold tailWord_3292726
  simp only [CollatzResearch.WordTrace]
  refine ⟨7505973966813970604669627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80063722312682353116476021 7505973966813970604669627)
  ·
    refine ⟨11258960950220955907004441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7505973966813970604669627 11258960950220955907004441)
    ·
      refine ⟨8444220712665716930253331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11258960950220955907004441 8444220712665716930253331)
      ·
        refine ⟨12666331068998575395379997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8444220712665716930253331 12666331068998575395379997)
        ·
          refine ⟨4749874150874465773267499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12666331068998575395379997 4749874150874465773267499)
          ·
            refine ⟨7124811226311698659901249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4749874150874465773267499 7124811226311698659901249)
            ·
              refine ⟨5343608419733773994925937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7124811226311698659901249 5343608419733773994925937)
              ·
                refine ⟨4007706314800330496194453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5343608419733773994925937 4007706314800330496194453)
                ·
                  refine ⟨187861233506265492009115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4007706314800330496194453 187861233506265492009115)
                  ·
                    rfl

theorem cell23_3292726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_3292726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292726 prefixEnd_3292726 := by exact prefixLift 3292726
  have htrace : WordTrace (prefixWord ++ tailWord_3292726) baseStart_3292726 baseEnd_3292726 := by
    simpa [prefixWord, tailWord_3292726, baseEnd_3292726] using wordTrace_append hprefix tailTrace_3292726
  have hstable : (prefixWord ++ tailWord_3292726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292726).length < 2 ^ (prefixWord ++ tailWord_3292726).sum := by decide
  have hdescent : baseEnd_3292726 < baseStart_3292726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292752 : List Nat := [2, 1, 1, 1, 1, 3, 6, 1, 1, 6]
def baseStart_3292752 : Nat := 118140960795 + 3292752 * 2 ^ 59
def prefixEnd_3292752 : Nat := 4983230072969 + 3 ^ 40 * 3292752 * 2
def baseEnd_3292752 : Nat := 563588150684468775452305

theorem tailTrace_3292752 : CollatzResearch.WordTrace tailWord_3292752 prefixEnd_3292752 563588150684468775452305 := by
  unfold tailWord_3292752
  simp only [CollatzResearch.WordTrace]
  refine ⟨60048265883464668057580255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80064354511286224076773673 60048265883464668057580255)
  ·
    refine ⟨90072398825197002086370383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60048265883464668057580255 90072398825197002086370383)
    ·
      refine ⟨135108598237795503129555575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90072398825197002086370383 135108598237795503129555575)
      ·
        refine ⟨202662897356693254694333363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135108598237795503129555575 202662897356693254694333363)
        ·
          refine ⟨303994346035039882041500045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202662897356693254694333363 303994346035039882041500045)
          ·
            refine ⟨113997879763139955765562517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303994346035039882041500045 113997879763139955765562517)
            ·
              refine ⟨5343650613897185426510743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113997879763139955765562517 5343650613897185426510743)
              ·
                refine ⟨8015475920845778139766115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5343650613897185426510743 8015475920845778139766115)
                ·
                  refine ⟨12023213881268667209649173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8015475920845778139766115 12023213881268667209649173)
                  ·
                    refine ⟨563588150684468775452305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12023213881268667209649173 563588150684468775452305)
                    ·
                      rfl

theorem cell23_3292752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 1, 6].length) (baseStart_3292752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292752 prefixEnd_3292752 := by exact prefixLift 3292752
  have htrace : WordTrace (prefixWord ++ tailWord_3292752) baseStart_3292752 baseEnd_3292752 := by
    simpa [prefixWord, tailWord_3292752, baseEnd_3292752] using wordTrace_append hprefix tailTrace_3292752
  have hstable : (prefixWord ++ tailWord_3292752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292752).length < 2 ^ (prefixWord ++ tailWord_3292752).sum := by decide
  have hdescent : baseEnd_3292752 < baseStart_3292752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292776 : List Nat := [2, 1, 4, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_3292776 : Nat := 118140960795 + 3292776 * 2 ^ 59
def prefixEnd_3292776 : Nat := 4983230072969 + 3 ^ 40 * 3292776 * 2
def baseEnd_3292776 : Nat := 1690776775589114232456805

theorem tailTrace_3292776 : CollatzResearch.WordTrace tailWord_3292776 prefixEnd_3292776 1690776775589114232456805 := by
  unfold tailWord_3292776
  simp only [CollatzResearch.WordTrace]
  refine ⟨60048703559421194107017091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80064938079228258809356121 60048703559421194107017091)
  ·
    refine ⟨90073055339131791160525637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60048703559421194107017091 90073055339131791160525637)
    ·
      refine ⟨16888697876087210842598557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90073055339131791160525637 16888697876087210842598557)
      ·
        refine ⟨6333261703532704065974459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16888697876087210842598557 6333261703532704065974459)
        ·
          refine ⟨9499892555299056098961689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6333261703532704065974459 9499892555299056098961689)
          ·
            refine ⟨7124919416474292074221267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9499892555299056098961689 7124919416474292074221267)
            ·
              refine ⟨10687379124711438111331901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7124919416474292074221267 10687379124711438111331901)
              ·
                refine ⟨4007767171766789291749463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10687379124711438111331901 4007767171766789291749463)
                ·
                  refine ⟨6011650757650183937624195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4007767171766789291749463 6011650757650183937624195)
                  ·
                    refine ⟨9017476136475275906436293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6011650757650183937624195 9017476136475275906436293)
                    ·
                      refine ⟨1690776775589114232456805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9017476136475275906436293 1690776775589114232456805)
                      ·
                        rfl

theorem cell23_3292776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_3292776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292776 prefixEnd_3292776 := by exact prefixLift 3292776
  have htrace : WordTrace (prefixWord ++ tailWord_3292776) baseStart_3292776 baseEnd_3292776 := by
    simpa [prefixWord, tailWord_3292776, baseEnd_3292776] using wordTrace_append hprefix tailTrace_3292776
  have hstable : (prefixWord ++ tailWord_3292776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292776).length < 2 ^ (prefixWord ++ tailWord_3292776).sum := by decide
  have hdescent : baseEnd_3292776 < baseStart_3292776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292786 : List Nat := [3, 2, 1, 2, 3, 1, 3, 2, 2, 4]
def baseStart_3292786 : Nat := 118140960795 + 3292786 * 2 ^ 59
def prefixEnd_3292786 : Nat := 4983230072969 + 3 ^ 40 * 3292786 * 2
def baseEnd_3292786 : Nat := 563593970131886397777253

theorem tailTrace_3292786 : CollatzResearch.WordTrace tailWord_3292786 prefixEnd_3292786 563593970131886397777253 := by
  unfold tailWord_3292786
  simp only [CollatzResearch.WordTrace]
  refine ⟨30024442962201539980474553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80065181232537439947932141 30024442962201539980474553)
  ·
    refine ⟨22518332221651154985355915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30024442962201539980474553 22518332221651154985355915)
    ·
      refine ⟨33777498332476732478033873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22518332221651154985355915 33777498332476732478033873)
      ·
        refine ⟨25333123749357549358525405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33777498332476732478033873 25333123749357549358525405)
        ·
          refine ⟨9499921406009081009447027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25333123749357549358525405 9499921406009081009447027)
          ·
            refine ⟨14249882109013621514170541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9499921406009081009447027 14249882109013621514170541)
            ·
              refine ⟨5343705790880108067813953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14249882109013621514170541 5343705790880108067813953)
              ·
                refine ⟨4007779343160081050860465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5343705790880108067813953 4007779343160081050860465)
                ·
                  refine ⟨3005834507370060788145349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4007779343160081050860465 3005834507370060788145349)
                  ·
                    refine ⟨563593970131886397777253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3005834507370060788145349 563593970131886397777253)
                    ·
                      rfl

theorem cell23_3292786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_3292786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292786 prefixEnd_3292786 := by exact prefixLift 3292786
  have htrace : WordTrace (prefixWord ++ tailWord_3292786) baseStart_3292786 baseEnd_3292786 := by
    simpa [prefixWord, tailWord_3292786, baseEnd_3292786] using wordTrace_append hprefix tailTrace_3292786
  have hstable : (prefixWord ++ tailWord_3292786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292786).length < 2 ^ (prefixWord ++ tailWord_3292786).sum := by decide
  have hdescent : baseEnd_3292786 < baseStart_3292786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292793 : List Nat := [1, 2, 1, 3, 3, 1, 1, 6, 1, 2, 2]
def baseStart_3292793 : Nat := 118140960795 + 3292793 * 2 ^ 59
def prefixEnd_3292793 : Nat := 4983230072969 + 3 ^ 40 * 3292793 * 2
def baseEnd_3292793 : Nat := 1690785504760240665944227

theorem tailTrace_3292793 : CollatzResearch.WordTrace tailWord_3292793 prefixEnd_3292793 1690785504760240665944227 := by
  unfold tailWord_3292793
  simp only [CollatzResearch.WordTrace]
  refine ⟨120098027159780800117403033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80065351439853866744935355 120098027159780800117403033)
  ·
    refine ⟨90073520369835600088052275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120098027159780800117403033 90073520369835600088052275)
    ·
      refine ⟨135110280554753400132078413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90073520369835600088052275 135110280554753400132078413)
      ·
        refine ⟨50666355208032525049529405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135110280554753400132078413 50666355208032525049529405)
        ·
          refine ⟨18999883203012196893573527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50666355208032525049529405 18999883203012196893573527)
          ·
            refine ⟨28499824804518295340360291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18999883203012196893573527 28499824804518295340360291)
            ·
              refine ⟨42749737206777443010540437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28499824804518295340360291 42749737206777443010540437)
              ·
                refine ⟨2003893931567692641119083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42749737206777443010540437 2003893931567692641119083)
                ·
                  refine ⟨3005840897351538961678625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2003893931567692641119083 3005840897351538961678625)
                  ·
                    refine ⟨2254380673013654221258969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3005840897351538961678625 2254380673013654221258969)
                    ·
                      refine ⟨1690785504760240665944227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2254380673013654221258969 1690785504760240665944227)
                      ·
                        rfl

theorem cell23_3292793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_3292793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292793 prefixEnd_3292793 := by exact prefixLift 3292793
  have htrace : WordTrace (prefixWord ++ tailWord_3292793) baseStart_3292793 baseEnd_3292793 := by
    simpa [prefixWord, tailWord_3292793, baseEnd_3292793] using wordTrace_append hprefix tailTrace_3292793
  have hstable : (prefixWord ++ tailWord_3292793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292793).length < 2 ^ (prefixWord ++ tailWord_3292793).sum := by decide
  have hdescent : baseEnd_3292793 < baseStart_3292793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292809 : List Nat := [1, 2, 1, 1, 4, 1, 5, 1, 1, 3, 3]
def baseStart_3292809 : Nat := 118140960795 + 3292809 * 2 ^ 59
def prefixEnd_3292809 : Nat := 4983230072969 + 3 ^ 40 * 3292809 * 2
def baseEnd_3292809 : Nat := 1690793720450712603344153

theorem tailTrace_3292809 : CollatzResearch.WordTrace tailWord_3292809 prefixEnd_3292809 1690793720450712603344153 := by
  unfold tailWord_3292809
  simp only [CollatzResearch.WordTrace]
  refine ⟨120098610727722834849985481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80065740485148556566656987 120098610727722834849985481)
  ·
    refine ⟨90073958045792126137489111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120098610727722834849985481 90073958045792126137489111)
    ·
      refine ⟨135110937068688189206233667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90073958045792126137489111 135110937068688189206233667)
      ·
        refine ⟨202666405603032283809350501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135110937068688189206233667 202666405603032283809350501)
        ·
          refine ⟨37999951050568553214253219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202666405603032283809350501 37999951050568553214253219)
          ·
            refine ⟨56999926575852829821379829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37999951050568553214253219 56999926575852829821379829)
            ·
              refine ⟨5343743116486202795754359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56999926575852829821379829 5343743116486202795754359)
              ·
                refine ⟨8015614674729304193631539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5343743116486202795754359 8015614674729304193631539)
                ·
                  refine ⟨12023422012093956290447309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8015614674729304193631539 12023422012093956290447309)
                  ·
                    refine ⟨4508783254535233608917741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12023422012093956290447309 4508783254535233608917741)
                    ·
                      refine ⟨1690793720450712603344153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4508783254535233608917741 1690793720450712603344153)
                      ·
                        rfl

theorem cell23_3292809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 3, 3].length) (baseStart_3292809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292809 prefixEnd_3292809 := by exact prefixLift 3292809
  have htrace : WordTrace (prefixWord ++ tailWord_3292809) baseStart_3292809 baseEnd_3292809 := by
    simpa [prefixWord, tailWord_3292809, baseEnd_3292809] using wordTrace_append hprefix tailTrace_3292809
  have hstable : (prefixWord ++ tailWord_3292809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292809).length < 2 ^ (prefixWord ++ tailWord_3292809).sum := by decide
  have hdescent : baseEnd_3292809 < baseStart_3292809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292860 : List Nat := [2, 2, 2, 3, 1, 4, 2, 1, 2, 1, 3]
def baseStart_3292860 : Nat := 118140960795 + 3292860 * 2 ^ 59
def prefixEnd_3292860 : Nat := 4983230072969 + 3 ^ 40 * 3292860 * 2
def baseEnd_3292860 : Nat := 1690819907964091903806419

theorem tailTrace_3292860 : CollatzResearch.WordTrace tailWord_3292860 prefixEnd_3292860 1690819907964091903806419 := by
  unfold tailWord_3292860
  simp only [CollatzResearch.WordTrace]
  refine ⟨60050235425269035280046017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80066980567025380373394689 60050235425269035280046017)
  ·
    refine ⟨45037676568951776460034513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60050235425269035280046017 45037676568951776460034513)
    ·
      refine ⟨33778257426713832345025885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45037676568951776460034513 33778257426713832345025885)
      ·
        refine ⟨12666846535017687129384707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33778257426713832345025885 12666846535017687129384707)
        ·
          refine ⟨19000269802526530694077061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12666846535017687129384707 19000269802526530694077061)
          ·
            refine ⟨3562550587973724505139449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19000269802526530694077061 3562550587973724505139449)
            ·
              refine ⟨2671912940980293378854587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3562550587973724505139449 2671912940980293378854587)
              ·
                refine ⟨4007869411470440068281881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671912940980293378854587 4007869411470440068281881)
                ·
                  refine ⟨3005902058602830051211411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4007869411470440068281881 3005902058602830051211411)
                  ·
                    refine ⟨4508853087904245076817117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3005902058602830051211411 4508853087904245076817117)
                    ·
                      refine ⟨1690819907964091903806419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4508853087904245076817117 1690819907964091903806419)
                      ·
                        rfl

theorem cell23_3292860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_3292860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292860 prefixEnd_3292860 := by exact prefixLift 3292860
  have htrace : WordTrace (prefixWord ++ tailWord_3292860) baseStart_3292860 baseEnd_3292860 := by
    simpa [prefixWord, tailWord_3292860, baseEnd_3292860] using wordTrace_append hprefix tailTrace_3292860
  have hstable : (prefixWord ++ tailWord_3292860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292860).length < 2 ^ (prefixWord ++ tailWord_3292860).sum := by decide
  have hdescent : baseEnd_3292860 < baseStart_3292860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292872 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 9]
def baseStart_3292872 : Nat := 118140960795 + 3292872 * 2 ^ 59
def prefixEnd_3292872 : Nat := 4983230072969 + 3 ^ 40 * 3292872 * 2
def baseEnd_3292872 : Nat := 187869563303549539650707

theorem tailTrace_3292872 : CollatzResearch.WordTrace tailWord_3292872 prefixEnd_3292872 187869563303549539650707 := by
  unfold tailWord_3292872
  simp only [CollatzResearch.WordTrace]
  refine ⟨60050454263247298304764435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80067272350996397739685913 60050454263247298304764435)
  ·
    refine ⟨90075681394870947457146653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60050454263247298304764435 90075681394870947457146653)
    ·
      refine ⟨33778380523076605296429995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90075681394870947457146653 33778380523076605296429995)
      ·
        refine ⟨50667570784614907944644993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33778380523076605296429995 50667570784614907944644993)
        ·
          refine ⟨38000678088461180958483745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50667570784614907944644993 38000678088461180958483745)
          ·
            refine ⟨28500508566345885718862809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38000678088461180958483745 28500508566345885718862809)
            ·
              refine ⟨21375381424759414289147107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28500508566345885718862809 21375381424759414289147107)
              ·
                refine ⟨32063072137139121433720661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21375381424759414289147107 32063072137139121433720661)
                ·
                  refine ⟨187869563303549539650707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32063072137139121433720661 187869563303549539650707)
                  ·
                    rfl

theorem cell23_3292872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 9].length) (baseStart_3292872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292872 prefixEnd_3292872 := by exact prefixLift 3292872
  have htrace : WordTrace (prefixWord ++ tailWord_3292872) baseStart_3292872 baseEnd_3292872 := by
    simpa [prefixWord, tailWord_3292872, baseEnd_3292872] using wordTrace_append hprefix tailTrace_3292872
  have hstable : (prefixWord ++ tailWord_3292872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292872).length < 2 ^ (prefixWord ++ tailWord_3292872).sum := by decide
  have hdescent : baseEnd_3292872 < baseStart_3292872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292912 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 7]
def baseStart_3292912 : Nat := 118140960795 + 3292912 * 2 ^ 59
def prefixEnd_3292912 : Nat := 4983230072969 + 3 ^ 40 * 3292912 * 2
def baseEnd_3292912 : Nat := 1690846608958125700356179

theorem tailTrace_3292912 : CollatzResearch.WordTrace tailWord_3292912 prefixEnd_3292912 1690846608958125700356179 := by
  unfold tailWord_3292912
  simp only [CollatzResearch.WordTrace]
  refine ⟨60051183723174841720492495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80068244964233122293989993 60051183723174841720492495)
  ·
    refine ⟨90076775584762262580738743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60051183723174841720492495 90076775584762262580738743)
    ·
      refine ⟨135115163377143393871108115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90076775584762262580738743 135115163377143393871108115)
      ·
        refine ⟨202672745065715090806662173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135115163377143393871108115 202672745065715090806662173)
        ·
          refine ⟨76002279399643159052498315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202672745065715090806662173 76002279399643159052498315)
          ·
            refine ⟨114003419099464738578747473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76002279399643159052498315 114003419099464738578747473)
            ·
              refine ⟨85502564324598553934060605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114003419099464738578747473 85502564324598553934060605)
              ·
                refine ⟨32063461621724457725272727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85502564324598553934060605 32063461621724457725272727)
                ·
                  refine ⟨48095192432586686587909091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32063461621724457725272727 48095192432586686587909091)
                  ·
                    refine ⟨72142788648880029881863637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48095192432586686587909091 72142788648880029881863637)
                    ·
                      refine ⟨1690846608958125700356179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72142788648880029881863637 1690846608958125700356179)
                      ·
                        rfl

theorem cell23_3292912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_3292912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292912 prefixEnd_3292912 := by exact prefixLift 3292912
  have htrace : WordTrace (prefixWord ++ tailWord_3292912) baseStart_3292912 baseEnd_3292912 := by
    simpa [prefixWord, tailWord_3292912, baseEnd_3292912] using wordTrace_append hprefix tailTrace_3292912
  have hstable : (prefixWord ++ tailWord_3292912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292912).length < 2 ^ (prefixWord ++ tailWord_3292912).sum := by decide
  have hdescent : baseEnd_3292912 < baseStart_3292912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292956 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 4, 4, 2]
def baseStart_3292956 : Nat := 118140960795 + 3292956 * 2 ^ 59
def prefixEnd_3292956 : Nat := 4983230072969 + 3 ^ 40 * 3292956 * 2
def baseEnd_3292956 : Nat := 1690869202106923528205977

theorem tailTrace_3292956 : CollatzResearch.WordTrace tailWord_3292956 prefixEnd_3292956 1690869202106923528205977 := by
  unfold tailWord_3292956
  simp only [CollatzResearch.WordTrace]
  refine ⟨60051986129095139477793361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80069314838793519303724481 60051986129095139477793361)
  ·
    refine ⟨45038989596821354608345021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60051986129095139477793361 45038989596821354608345021)
    ·
      refine ⟨16889621098808007978129383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45038989596821354608345021 16889621098808007978129383)
      ·
        refine ⟨25334431648212011967194075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16889621098808007978129383 25334431648212011967194075)
        ·
          refine ⟨38001647472318017950791113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25334431648212011967194075 38001647472318017950791113)
          ·
            refine ⟨28501235604238513463093335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38001647472318017950791113 28501235604238513463093335)
            ·
              refine ⟨42751853406357770194640003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28501235604238513463093335 42751853406357770194640003)
              ·
                refine ⟨64127780109536655291960005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42751853406357770194640003 64127780109536655291960005)
                ·
                  refine ⟨12023958770538122867242501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64127780109536655291960005 12023958770538122867242501)
                  ·
                    refine ⟨2254492269475898037607969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12023958770538122867242501 2254492269475898037607969)
                    ·
                      refine ⟨1690869202106923528205977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2254492269475898037607969 1690869202106923528205977)
                      ·
                        rfl

theorem cell23_3292956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_3292956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3292956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3292956 prefixEnd_3292956 := by exact prefixLift 3292956
  have htrace : WordTrace (prefixWord ++ tailWord_3292956) baseStart_3292956 baseEnd_3292956 := by
    simpa [prefixWord, tailWord_3292956, baseEnd_3292956] using wordTrace_append hprefix tailTrace_3292956
  have hstable : (prefixWord ++ tailWord_3292956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292956).length < 2 ^ (prefixWord ++ tailWord_3292956).sum := by decide
  have hdescent : baseEnd_3292956 < baseStart_3292956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293000 : List Nat := [2, 1, 3, 1, 1, 6, 1, 3, 1, 4]
def baseStart_3293000 : Nat := 118140960795 + 3293000 * 2 ^ 59
def prefixEnd_3293000 : Nat := 4983230072969 + 3 ^ 40 * 3293000 * 2
def baseEnd_3293000 : Nat := 563630598418573785351925

theorem tailTrace_3293000 : CollatzResearch.WordTrace tailWord_3293000 prefixEnd_3293000 563630598418573785351925 := by
  unfold tailWord_3293000
  simp only [CollatzResearch.WordTrace]
  refine ⟨60052788535015437235094227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80070384713353916313458969 60052788535015437235094227)
  ·
    refine ⟨90079182802523155852641341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60052788535015437235094227 90079182802523155852641341)
    ·
      refine ⟨33779693550946183444740503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90079182802523155852641341 33779693550946183444740503)
      ·
        refine ⟨50669540326419275167110755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33779693550946183444740503 50669540326419275167110755)
        ·
          refine ⟨76004310489628912750666133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50669540326419275167110755 76004310489628912750666133)
          ·
            refine ⟨3562702054201355285187475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 76004310489628912750666133 3562702054201355285187475)
            ·
              refine ⟨5344053081302032927781213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3562702054201355285187475 5344053081302032927781213)
              ·
                refine ⟨2004019905488262347917955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5344053081302032927781213 2004019905488262347917955)
                ·
                  refine ⟨3006029858232393521876933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2004019905488262347917955 3006029858232393521876933)
                  ·
                    refine ⟨563630598418573785351925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3006029858232393521876933 563630598418573785351925)
                    ·
                      rfl

theorem cell23_3293000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_3293000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293000 prefixEnd_3293000 := by exact prefixLift 3293000
  have htrace : WordTrace (prefixWord ++ tailWord_3293000) baseStart_3293000 baseEnd_3293000 := by
    simpa [prefixWord, tailWord_3293000, baseEnd_3293000] using wordTrace_append hprefix tailTrace_3293000
  have hstable : (prefixWord ++ tailWord_3293000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293000).length < 2 ^ (prefixWord ++ tailWord_3293000).sum := by decide
  have hdescent : baseEnd_3293000 < baseStart_3293000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293023 : List Nat := [1, 1, 2, 3, 1, 4, 3, 1, 3, 1, 3]
def baseStart_3293023 : Nat := 118140960795 + 3293023 * 2 ^ 59
def prefixEnd_3293023 : Nat := 4983230072969 + 3 ^ 40 * 3293023 * 2
def baseEnd_3293023 : Nat := 1690903605310774766068169

theorem tailTrace_3293023 : CollatzResearch.WordTrace tailWord_3293023 prefixEnd_3293023 1690903605310774766068169 := by
  unfold tailWord_3293023
  simp only [CollatzResearch.WordTrace]
  refine ⟨120106415948947549398275723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80070943965965032932183815 120106415948947549398275723)
  ·
    refine ⟨180159623923421324097413585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120106415948947549398275723 180159623923421324097413585)
    ·
      refine ⟨135119717942565993073060189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180159623923421324097413585 135119717942565993073060189)
      ·
        refine ⟨50669894228462247402397571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135119717942565993073060189 50669894228462247402397571)
        ·
          refine ⟨76004841342693371103596357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50669894228462247402397571 76004841342693371103596357)
          ·
            refine ⟨14250907751755007081924317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76004841342693371103596357 14250907751755007081924317)
            ·
              refine ⟨5344090406908127655721619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14250907751755007081924317 5344090406908127655721619)
              ·
                refine ⟨8016135610362191483582429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5344090406908127655721619 8016135610362191483582429)
                ·
                  refine ⟨3006050853885821806343411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8016135610362191483582429 3006050853885821806343411)
                  ·
                    refine ⟨4509076280828732709515117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3006050853885821806343411 4509076280828732709515117)
                    ·
                      refine ⟨1690903605310774766068169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4509076280828732709515117 1690903605310774766068169)
                      ·
                        rfl

theorem cell23_3293023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_3293023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293023 prefixEnd_3293023 := by exact prefixLift 3293023
  have htrace : WordTrace (prefixWord ++ tailWord_3293023) baseStart_3293023 baseEnd_3293023 := by
    simpa [prefixWord, tailWord_3293023, baseEnd_3293023] using wordTrace_append hprefix tailTrace_3293023
  have hstable : (prefixWord ++ tailWord_3293023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293023).length < 2 ^ (prefixWord ++ tailWord_3293023).sum := by decide
  have hdescent : baseEnd_3293023 < baseStart_3293023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293029 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 2, 5, 4]
def baseStart_3293029 : Nat := 118140960795 + 3293029 * 2 ^ 59
def prefixEnd_3293029 : Nat := 4983230072969 + 3 ^ 40 * 3293029 * 2
def baseEnd_3293029 : Nat := 1690906686194701742593141

theorem tailTrace_3293029 : CollatzResearch.WordTrace tailWord_3293029 prefixEnd_3293029 1690906686194701742593141 := by
  unfold tailWord_3293029
  simp only [CollatzResearch.WordTrace]
  refine ⟨120106634786925812422994141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80071089857950541615329427 120106634786925812422994141)
  ·
    refine ⟨45039988045097179658622803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120106634786925812422994141 45039988045097179658622803)
    ·
      refine ⟨67559982067645769487934205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45039988045097179658622803 67559982067645769487934205)
      ·
        refine ⟨25334993275367163557975327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67559982067645769487934205 25334993275367163557975327)
        ·
          refine ⟨38002489913050745336962991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25334993275367163557975327 38002489913050745336962991)
          ·
            refine ⟨57003734869576118005444487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38002489913050745336962991 57003734869576118005444487)
            ·
              refine ⟨85505602304364177008166731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57003734869576118005444487 85505602304364177008166731)
              ·
                refine ⟨128258403456546265512250097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85505602304364177008166731 128258403456546265512250097)
                ·
                  refine ⟨96193802592409699134187573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128258403456546265512250097 96193802592409699134187573)
                  ·
                    refine ⟨9018168993038409293830085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96193802592409699134187573 9018168993038409293830085)
                    ·
                      refine ⟨1690906686194701742593141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9018168993038409293830085 1690906686194701742593141)
                      ·
                        rfl

theorem cell23_3293029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_3293029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293029 prefixEnd_3293029 := by exact prefixLift 3293029
  have htrace : WordTrace (prefixWord ++ tailWord_3293029) baseStart_3293029 baseEnd_3293029 := by
    simpa [prefixWord, tailWord_3293029, baseEnd_3293029] using wordTrace_append hprefix tailTrace_3293029
  have hstable : (prefixWord ++ tailWord_3293029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293029).length < 2 ^ (prefixWord ++ tailWord_3293029).sum := by decide
  have hdescent : baseEnd_3293029 < baseStart_3293029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293074 : List Nat := [3, 2, 3, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_3293074 : Nat := 118140960795 + 3293074 * 2 ^ 59
def prefixEnd_3293074 : Nat := 4983230072969 + 3 ^ 40 * 3293074 * 2
def baseEnd_3293074 : Nat := 1690929792824154066530435

theorem tailTrace_3293074 : CollatzResearch.WordTrace tailWord_3293074 prefixEnd_3293074 1690929792824154066530435 := by
  unfold tailWord_3293074
  simp only [CollatzResearch.WordTrace]
  refine ⟨30027069017940696277095569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80072184047841856738921517 30027069017940696277095569)
  ·
    refine ⟨22520301763455522207821677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30027069017940696277095569 22520301763455522207821677)
    ·
      refine ⟨8445113161295820827933129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22520301763455522207821677 8445113161295820827933129)
      ·
        refine ⟨6333834870971865620949847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8445113161295820827933129 6333834870971865620949847)
        ·
          refine ⟨9500752306457798431424771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6333834870971865620949847 9500752306457798431424771)
          ·
            refine ⟨14251128459686697647137157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9500752306457798431424771 14251128459686697647137157)
            ·
              refine ⟨2672086586191255808838217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14251128459686697647137157 2672086586191255808838217)
              ·
                refine ⟨2004064939643441856628663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2672086586191255808838217 2004064939643441856628663)
                ·
                  refine ⟨3006097409465162784942995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2004064939643441856628663 3006097409465162784942995)
                  ·
                    refine ⟨4509146114197744177414493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3006097409465162784942995 4509146114197744177414493)
                    ·
                      refine ⟨1690929792824154066530435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4509146114197744177414493 1690929792824154066530435)
                      ·
                        rfl

theorem cell23_3293074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_3293074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293074 prefixEnd_3293074 := by exact prefixLift 3293074
  have htrace : WordTrace (prefixWord ++ tailWord_3293074) baseStart_3293074 baseEnd_3293074 := by
    simpa [prefixWord, tailWord_3293074, baseEnd_3293074] using wordTrace_append hprefix tailTrace_3293074
  have hstable : (prefixWord ++ tailWord_3293074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293074).length < 2 ^ (prefixWord ++ tailWord_3293074).sum := by decide
  have hdescent : baseEnd_3293074 < baseStart_3293074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293113 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 4, 1, 3]
def baseStart_3293113 : Nat := 118140960795 + 3293113 * 2 ^ 59
def prefixEnd_3293113 : Nat := 4983230072969 + 3 ^ 40 * 3293113 * 2
def baseEnd_3293113 : Nat := 1690949818569679413942755

theorem tailTrace_3293113 : CollatzResearch.WordTrace tailWord_3293113 prefixEnd_3293113 1690949818569679413942755 := by
  unfold tailWord_3293113
  simp only [CollatzResearch.WordTrace]
  refine ⟨120109698518621494769051993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80073132345747663179367995 120109698518621494769051993)
  ·
    refine ⟨90082273888966121076788995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120109698518621494769051993 90082273888966121076788995)
    ·
      refine ⟨135123410833449181615183493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90082273888966121076788995 135123410833449181615183493)
      ·
        refine ⟨25335639531271721552846905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135123410833449181615183493 25335639531271721552846905)
        ·
          refine ⟨19001729648453791164635179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25335639531271721552846905 19001729648453791164635179)
          ·
            refine ⟨28502594472680686746952769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19001729648453791164635179 28502594472680686746952769)
            ·
              refine ⟨21376945854510515060214577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28502594472680686746952769 21376945854510515060214577)
              ·
                refine ⟨16032709390882886295160933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21376945854510515060214577 16032709390882886295160933)
                ·
                  refine ⟨3006133010790541180342675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16032709390882886295160933 3006133010790541180342675)
                  ·
                    refine ⟨4509199516185811770514013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3006133010790541180342675 4509199516185811770514013)
                    ·
                      refine ⟨1690949818569679413942755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4509199516185811770514013 1690949818569679413942755)
                      ·
                        rfl

theorem cell23_3293113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_3293113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293113 prefixEnd_3293113 := by exact prefixLift 3293113
  have htrace : WordTrace (prefixWord ++ tailWord_3293113) baseStart_3293113 baseEnd_3293113 := by
    simpa [prefixWord, tailWord_3293113, baseEnd_3293113] using wordTrace_append hprefix tailTrace_3293113
  have hstable : (prefixWord ++ tailWord_3293113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293113).length < 2 ^ (prefixWord ++ tailWord_3293113).sum := by decide
  have hdescent : baseEnd_3293113 < baseStart_3293113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293117 : List Nat := [1, 4, 1, 2, 3, 3, 2, 1, 1, 2, 3]
def baseStart_3293117 : Nat := 118140960795 + 3293117 * 2 ^ 59
def prefixEnd_3293117 : Nat := 4983230072969 + 3 ^ 40 * 3293117 * 2
def baseEnd_3293117 : Nat := 1690951872492297398292737

theorem tailTrace_3293117 : CollatzResearch.WordTrace tailWord_3293117 prefixEnd_3293117 1690951872492297398292737 := by
  unfold tailWord_3293117
  simp only [CollatzResearch.WordTrace]
  refine ⟨120109844410607003452197605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80073229607071335634798403 120109844410607003452197605)
  ·
    refine ⟨22520595826988813147287051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120109844410607003452197605 22520595826988813147287051)
    ·
      refine ⟨33780893740483219720930577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22520595826988813147287051 33780893740483219720930577)
      ·
        refine ⟨25335670305362414790697933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33780893740483219720930577 25335670305362414790697933)
        ·
          refine ⟨9500876364510905546511725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25335670305362414790697933 9500876364510905546511725)
          ·
            refine ⟨3562828636691589579941897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9500876364510905546511725 3562828636691589579941897)
            ·
              refine ⟨2672121477518692184956423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3562828636691589579941897 2672121477518692184956423)
              ·
                refine ⟨4008182216278038277434635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2672121477518692184956423 4008182216278038277434635)
                ·
                  refine ⟨6012273324417057416151953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4008182216278038277434635 6012273324417057416151953)
                  ·
                    refine ⟨4509204993312793062113965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6012273324417057416151953 4509204993312793062113965)
                    ·
                      refine ⟨1690951872492297398292737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4509204993312793062113965 1690951872492297398292737)
                      ·
                        rfl

theorem cell23_3293117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_3293117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293117 prefixEnd_3293117 := by exact prefixLift 3293117
  have htrace : WordTrace (prefixWord ++ tailWord_3293117) baseStart_3293117 baseEnd_3293117 := by
    simpa [prefixWord, tailWord_3293117, baseEnd_3293117] using wordTrace_append hprefix tailTrace_3293117
  have hstable : (prefixWord ++ tailWord_3293117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293117).length < 2 ^ (prefixWord ++ tailWord_3293117).sum := by decide
  have hdescent : baseEnd_3293117 < baseStart_3293117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293129 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 3, 8]
def baseStart_3293129 : Nat := 118140960795 + 3293129 * 2 ^ 59
def prefixEnd_3293129 : Nat := 4983230072969 + 3 ^ 40 * 3293129 * 2
def baseEnd_3293129 : Nat := 563652678086717117114227

theorem tailTrace_3293129 : CollatzResearch.WordTrace tailWord_3293129 prefixEnd_3293129 563652678086717117114227 := by
  unfold tailWord_3293129
  simp only [CollatzResearch.WordTrace]
  refine ⟨120110282086563529501634441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80073521391042353001089627 120110282086563529501634441)
  ·
    refine ⟨90082711564922647126225831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120110282086563529501634441 90082711564922647126225831)
    ·
      refine ⟨135124067347383970689338747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90082711564922647126225831 135124067347383970689338747)
      ·
        refine ⟨202686101021075956034008121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135124067347383970689338747 202686101021075956034008121)
        ·
          refine ⟨152014575765806967025506091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202686101021075956034008121 152014575765806967025506091)
          ·
            refine ⟨228021863648710450538259137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152014575765806967025506091 228021863648710450538259137)
            ·
              refine ⟨171016397736532837903694353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228021863648710450538259137 171016397736532837903694353)
              ·
                refine ⟨128262298302399628427770765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171016397736532837903694353 128262298302399628427770765)
                ·
                  refine ⟨48098361863399860660414037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128262298302399628427770765 48098361863399860660414037)
                  ·
                    refine ⟨563652678086717117114227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48098361863399860660414037 563652678086717117114227)
                    ·
                      rfl

theorem cell23_3293129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 8].length) (baseStart_3293129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293129 prefixEnd_3293129 := by exact prefixLift 3293129
  have htrace : WordTrace (prefixWord ++ tailWord_3293129) baseStart_3293129 baseEnd_3293129 := by
    simpa [prefixWord, tailWord_3293129, baseEnd_3293129] using wordTrace_append hprefix tailTrace_3293129
  have hstable : (prefixWord ++ tailWord_3293129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293129).length < 2 ^ (prefixWord ++ tailWord_3293129).sum := by decide
  have hdescent : baseEnd_3293129 < baseStart_3293129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293130 : List Nat := [3, 1, 2, 1, 2, 1, 5, 2, 2, 1, 3]
def baseStart_3293130 : Nat := 118140960795 + 3293130 * 2 ^ 59
def prefixEnd_3293130 : Nat := 4983230072969 + 3 ^ 40 * 3293130 * 2
def baseEnd_3293130 : Nat := 1690958547740805847430177

theorem tailTrace_3293130 : CollatzResearch.WordTrace tailWord_3293130 prefixEnd_3293130 1690958547740805847430177 := by
  unfold tailWord_3293130
  simp only [CollatzResearch.WordTrace]
  refine ⟨30027579639889976668105211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80073545706373271114947229 30027579639889976668105211)
  ·
    refine ⟨45041369459834965002157817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30027579639889976668105211 45041369459834965002157817)
    ·
      refine ⟨33781027094876223751618363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45041369459834965002157817 33781027094876223751618363)
      ·
        refine ⟨50671540642314335627427545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33781027094876223751618363 50671540642314335627427545)
        ·
          refine ⟨38003655481735751720570659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50671540642314335627427545 38003655481735751720570659)
          ·
            refine ⟨57005483222603627580855989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38003655481735751720570659 57005483222603627580855989)
            ·
              refine ⟨5344264052119090085705249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57005483222603627580855989 5344264052119090085705249)
              ·
                refine ⟨4008198039089317564278937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5344264052119090085705249 4008198039089317564278937)
                ·
                  refine ⟨3006148529316988173209203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4008198039089317564278937 3006148529316988173209203)
                  ·
                    refine ⟨4509222793975482259813805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3006148529316988173209203 4509222793975482259813805)
                    ·
                      refine ⟨1690958547740805847430177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4509222793975482259813805 1690958547740805847430177)
                      ·
                        rfl

theorem cell23_3293130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_3293130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293130 prefixEnd_3293130 := by exact prefixLift 3293130
  have htrace : WordTrace (prefixWord ++ tailWord_3293130) baseStart_3293130 baseEnd_3293130 := by
    simpa [prefixWord, tailWord_3293130, baseEnd_3293130] using wordTrace_append hprefix tailTrace_3293130
  have hstable : (prefixWord ++ tailWord_3293130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293130).length < 2 ^ (prefixWord ++ tailWord_3293130).sum := by decide
  have hdescent : baseEnd_3293130 < baseStart_3293130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293156 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_3293156 : Nat := 118140960795 + 3293156 * 2 ^ 59
def prefixEnd_3293156 : Nat := 4983230072969 + 3 ^ 40 * 3293156 * 2
def baseEnd_3293156 : Nat := 1690971898237822745705057

theorem tailTrace_3293156 : CollatzResearch.WordTrace tailWord_3293156 prefixEnd_3293156 1690971898237822745705057 := by
  unfold tailWord_3293156
  simp only [CollatzResearch.WordTrace]
  refine ⟨60055633428732856556433661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80074177904977142075244881 60055633428732856556433661)
  ·
    refine ⟨22520862535774821208662623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60055633428732856556433661 22520862535774821208662623)
    ·
      refine ⟨33781293803662231812993935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22520862535774821208662623 33781293803662231812993935)
      ·
        refine ⟨50671940705493347719490903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33781293803662231812993935 50671940705493347719490903)
        ·
          refine ⟨76007911058240021579236355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50671940705493347719490903 76007911058240021579236355)
          ·
            refine ⟨114011866587360032368854533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76007911058240021579236355 114011866587360032368854533)
            ·
              refine ⟨21377224985130006069160225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114011866587360032368854533 21377224985130006069160225)
              ·
                refine ⟨16032918738847504551870169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21377224985130006069160225 16032918738847504551870169)
                ·
                  refine ⟨12024689054135628413902627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16032918738847504551870169 12024689054135628413902627)
                  ·
                    refine ⟨18037033581203442620853941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12024689054135628413902627 18037033581203442620853941)
                    ·
                      refine ⟨1690971898237822745705057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18037033581203442620853941 1690971898237822745705057)
                      ·
                        rfl

theorem cell23_3293156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_3293156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293156 prefixEnd_3293156 := by exact prefixLift 3293156
  have htrace : WordTrace (prefixWord ++ tailWord_3293156) baseStart_3293156 baseEnd_3293156 := by
    simpa [prefixWord, tailWord_3293156, baseEnd_3293156] using wordTrace_append hprefix tailTrace_3293156
  have hstable : (prefixWord ++ tailWord_3293156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293156).length < 2 ^ (prefixWord ++ tailWord_3293156).sum := by decide
  have hdescent : baseEnd_3293156 < baseStart_3293156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293243 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 4, 4, 2]
def baseStart_3293243 : Nat := 118140960795 + 3293243 * 2 ^ 59
def prefixEnd_3293243 : Nat := 4983230072969 + 3 ^ 40 * 3293243 * 2
def baseEnd_3293243 : Nat := 1691016571054763905317157

theorem tailTrace_3293243 : CollatzResearch.WordTrace tailWord_3293243 prefixEnd_3293243 1691016571054763905317157 := by
  unfold tailWord_3293243
  simp only [CollatzResearch.WordTrace]
  refine ⟨120114440008150526971284383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80076293338767017980856255 120114440008150526971284383)
  ·
    refine ⟨180171660012225790456926575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120114440008150526971284383 180171660012225790456926575)
    ·
      refine ⟨270257490018338685685389863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180171660012225790456926575 270257490018338685685389863)
      ·
        refine ⟨405386235027508028528084795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270257490018338685685389863 405386235027508028528084795)
        ·
          refine ⟨608079352541262042792127193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405386235027508028528084795 608079352541262042792127193)
          ·
            refine ⟨456059514405946532094095395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 608079352541262042792127193 456059514405946532094095395)
            ·
              refine ⟨684089271608919798141143093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456059514405946532094095395 684089271608919798141143093)
              ·
                refine ⟨64133369213336231075732165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 684089271608919798141143093 64133369213336231075732165)
                ·
                  refine ⟨12025006727500543326699781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64133369213336231075732165 12025006727500543326699781)
                  ·
                    refine ⟨2254688761406351873756209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12025006727500543326699781 2254688761406351873756209)
                    ·
                      refine ⟨1691016571054763905317157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2254688761406351873756209 1691016571054763905317157)
                      ·
                        rfl

theorem cell23_3293243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 4, 2].length) (baseStart_3293243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293243 prefixEnd_3293243 := by exact prefixLift 3293243
  have htrace : WordTrace (prefixWord ++ tailWord_3293243) baseStart_3293243 baseEnd_3293243 := by
    simpa [prefixWord, tailWord_3293243, baseEnd_3293243] using wordTrace_append hprefix tailTrace_3293243
  have hstable : (prefixWord ++ tailWord_3293243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293243).length < 2 ^ (prefixWord ++ tailWord_3293243).sum := by decide
  have hdescent : baseEnd_3293243 < baseStart_3293243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293253 : List Nat := [1, 3, 1, 1, 1, 3, 1, 5, 3, 4]
def baseStart_3293253 : Nat := 118140960795 + 3293253 * 2 ^ 59
def prefixEnd_3293253 : Nat := 4983230072969 + 3 ^ 40 * 3293253 * 2
def baseEnd_3293253 : Nat := 563673901953769622064037

theorem tailTrace_3293253 : CollatzResearch.WordTrace tailWord_3293253 prefixEnd_3293253 563673901953769622064037 := by
  unfold tailWord_3293253
  simp only [CollatzResearch.WordTrace]
  refine ⟨120114804738114298679148413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80076536492076199119432275 120114804738114298679148413)
  ·
    refine ⟨45043051776792862004680655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120114804738114298679148413 45043051776792862004680655)
    ·
      refine ⟨67564577665189293007020983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45043051776792862004680655 67564577665189293007020983)
      ·
        refine ⟨101346866497783939510531475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67564577665189293007020983 101346866497783939510531475)
        ·
          refine ⟨152020299746675909265797213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101346866497783939510531475 152020299746675909265797213)
          ·
            refine ⟨57007612405003465974673955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152020299746675909265797213 57007612405003465974673955)
            ·
              refine ⟨85511418607505198962010933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57007612405003465974673955 85511418607505198962010933)
              ·
                refine ⟨8016695494453612402688525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85511418607505198962010933 8016695494453612402688525)
                ·
                  refine ⟨3006260810420104651008197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8016695494453612402688525 3006260810420104651008197)
                  ·
                    refine ⟨563673901953769622064037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3006260810420104651008197 563673901953769622064037)
                    ·
                      rfl

theorem cell23_3293253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_3293253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293253 prefixEnd_3293253 := by exact prefixLift 3293253
  have htrace : WordTrace (prefixWord ++ tailWord_3293253) baseStart_3293253 baseEnd_3293253 := by
    simpa [prefixWord, tailWord_3293253, baseEnd_3293253] using wordTrace_append hprefix tailTrace_3293253
  have hstable : (prefixWord ++ tailWord_3293253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293253).length < 2 ^ (prefixWord ++ tailWord_3293253).sum := by decide
  have hdescent : baseEnd_3293253 < baseStart_3293253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293256 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_3293256 : Nat := 118140960795 + 3293256 * 2 ^ 59
def prefixEnd_3293256 : Nat := 4983230072969 + 3 ^ 40 * 3293256 * 2
def baseEnd_3293256 : Nat := 1691023246303272354454597

theorem tailTrace_3293256 : CollatzResearch.WordTrace tailWord_3293256 prefixEnd_3293256 1691023246303272354454597 := by
  unfold tailWord_3293256
  simp only [CollatzResearch.WordTrace]
  refine ⟨60057457078551715095753811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80076609438068953461005081 60057457078551715095753811)
  ·
    refine ⟨90086185617827572643630717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60057457078551715095753811 90086185617827572643630717)
    ·
      refine ⟨33782319606685339741361519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90086185617827572643630717 33782319606685339741361519)
      ·
        refine ⟨50673479410028009612042279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33782319606685339741361519 50673479410028009612042279)
        ·
          refine ⟨76010219115042014418063419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50673479410028009612042279 76010219115042014418063419)
          ·
            refine ⟨114015328672563021627095129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76010219115042014418063419 114015328672563021627095129)
            ·
              refine ⟨85511496504422266220321347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114015328672563021627095129 85511496504422266220321347)
              ·
                refine ⟨128267244756633399330482021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85511496504422266220321347 128267244756633399330482021)
                ·
                  refine ⟨24050108391868762374465379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128267244756633399330482021 24050108391868762374465379)
                  ·
                    refine ⟨36075162587803143561698069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24050108391868762374465379 36075162587803143561698069)
                    ·
                      refine ⟨1691023246303272354454597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36075162587803143561698069 1691023246303272354454597)
                      ·
                        rfl

theorem cell23_3293256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_3293256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293256 prefixEnd_3293256 := by exact prefixLift 3293256
  have htrace : WordTrace (prefixWord ++ tailWord_3293256) baseStart_3293256 baseEnd_3293256 := by
    simpa [prefixWord, tailWord_3293256, baseEnd_3293256] using wordTrace_append hprefix tailTrace_3293256
  have hstable : (prefixWord ++ tailWord_3293256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293256).length < 2 ^ (prefixWord ++ tailWord_3293256).sum := by decide
  have hdescent : baseEnd_3293256 < baseStart_3293256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293277 : List Nat := [1, 4, 4, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3293277 : Nat := 118140960795 + 3293277 * 2 ^ 59
def prefixEnd_3293277 : Nat := 4983230072969 + 3 ^ 40 * 3293277 * 2
def baseEnd_3293277 : Nat := 1691034029397016772292001

theorem tailTrace_3293277 : CollatzResearch.WordTrace tailWord_3293277 prefixEnd_3293277 1691034029397016772292001 := by
  unfold tailWord_3293277
  simp only [CollatzResearch.WordTrace]
  refine ⟨120115680090027350778022085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80077120060018233852014723 120115680090027350778022085)
  ·
    refine ⟨22521690016880128270879141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120115680090027350778022085 22521690016880128270879141)
    ·
      refine ⟨4222816878165024050789839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22521690016880128270879141 4222816878165024050789839)
      ·
        refine ⟨6334225317247536076184759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4222816878165024050789839 6334225317247536076184759)
        ·
          refine ⟨9501337975871304114277139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6334225317247536076184759 9501337975871304114277139)
          ·
            refine ⟨14252006963806956171415709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9501337975871304114277139 14252006963806956171415709)
            ·
              refine ⟨5344502611427608564280891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14252006963806956171415709 5344502611427608564280891)
              ·
                refine ⟨8016753917141412846421337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5344502611427608564280891 8016753917141412846421337)
                ·
                  refine ⟨6012565437856059634816003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8016753917141412846421337 6012565437856059634816003)
                  ·
                    refine ⟨9018848156784089452224005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6012565437856059634816003 9018848156784089452224005)
                    ·
                      refine ⟨1691034029397016772292001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9018848156784089452224005 1691034029397016772292001)
                      ·
                        rfl

theorem cell23_3293277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3293277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293277 prefixEnd_3293277 := by exact prefixLift 3293277
  have htrace : WordTrace (prefixWord ++ tailWord_3293277) baseStart_3293277 baseEnd_3293277 := by
    simpa [prefixWord, tailWord_3293277, baseEnd_3293277] using wordTrace_append hprefix tailTrace_3293277
  have hstable : (prefixWord ++ tailWord_3293277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293277).length < 2 ^ (prefixWord ++ tailWord_3293277).sum := by decide
  have hdescent : baseEnd_3293277 < baseStart_3293277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293280 : List Nat := [2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 3]
def baseStart_3293280 : Nat := 118140960795 + 3293280 * 2 ^ 59
def prefixEnd_3293280 : Nat := 4983230072969 + 3 ^ 40 * 3293280 * 2
def baseEnd_3293280 : Nat := 1691035569838980260554487

theorem tailTrace_3293280 : CollatzResearch.WordTrace tailWord_3293280 prefixEnd_3293280 1691035569838980260554487 := by
  unfold tailWord_3293280
  simp only [CollatzResearch.WordTrace]
  refine ⟨60057894754508241145190647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80077193006010988193587529 60057894754508241145190647)
  ·
    refine ⟨90086842131762361717785971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60057894754508241145190647 90086842131762361717785971)
    ·
      refine ⟨135130263197643542576678957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90086842131762361717785971 135130263197643542576678957)
      ·
        refine ⟨50673848699116328466254609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135130263197643542576678957 50673848699116328466254609)
        ·
          refine ⟨38005386524337246349690957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50673848699116328466254609 38005386524337246349690957)
          ·
            refine ⟨14252019946626467381134109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38005386524337246349690957 14252019946626467381134109)
            ·
              refine ⟨5344507479984925267925291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14252019946626467381134109 5344507479984925267925291)
              ·
                refine ⟨8016761219977387901887937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5344507479984925267925291 8016761219977387901887937)
                ·
                  refine ⟨6012570914983040926415953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8016761219977387901887937 6012570914983040926415953)
                  ·
                    refine ⟨4509428186237280694811965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6012570914983040926415953 4509428186237280694811965)
                    ·
                      refine ⟨1691035569838980260554487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4509428186237280694811965 1691035569838980260554487)
                      ·
                        rfl

theorem cell23_3293280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_3293280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293280 prefixEnd_3293280 := by exact prefixLift 3293280
  have htrace : WordTrace (prefixWord ++ tailWord_3293280) baseStart_3293280 baseEnd_3293280 := by
    simpa [prefixWord, tailWord_3293280, baseEnd_3293280] using wordTrace_append hprefix tailTrace_3293280
  have hstable : (prefixWord ++ tailWord_3293280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293280).length < 2 ^ (prefixWord ++ tailWord_3293280).sum := by decide
  have hdescent : baseEnd_3293280 < baseStart_3293280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293287 : List Nat := [1, 1, 5, 1, 1, 2, 4, 3, 1, 4]
def baseStart_3293287 : Nat := 118140960795 + 3293287 * 2 ^ 59
def prefixEnd_3293287 : Nat := 4983230072969 + 3 ^ 40 * 3293287 * 2
def baseEnd_3293287 : Nat := 563679721401187244388985

theorem tailTrace_3293287 : CollatzResearch.WordTrace tailWord_3293287 prefixEnd_3293287 563679721401187244388985 := by
  unfold tailWord_3293287
  simp only [CollatzResearch.WordTrace]
  refine ⟨120116044819991122485886115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80077363213327414990590743 120116044819991122485886115)
  ·
    refine ⟨180174067229986683728829173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120116044819991122485886115 180174067229986683728829173)
    ·
      refine ⟨16891318802811251599577735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180174067229986683728829173 16891318802811251599577735)
      ·
        refine ⟨25336978204216877399366603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16891318802811251599577735 25336978204216877399366603)
        ·
          refine ⟨38005467306325316099049905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25336978204216877399366603 38005467306325316099049905)
          ·
            refine ⟨28504100479743987074287429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38005467306325316099049905 28504100479743987074287429)
            ·
              refine ⟨5344518839951997576428893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28504100479743987074287429 5344518839951997576428893)
              ·
                refine ⟨2004194564981999091160835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5344518839951997576428893 2004194564981999091160835)
                ·
                  refine ⟨3006291847472998636741253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2004194564981999091160835 3006291847472998636741253)
                  ·
                    refine ⟨563679721401187244388985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3006291847472998636741253 563679721401187244388985)
                    ·
                      rfl

theorem cell23_3293287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_3293287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293287 prefixEnd_3293287 := by exact prefixLift 3293287
  have htrace : WordTrace (prefixWord ++ tailWord_3293287) baseStart_3293287 baseEnd_3293287 := by
    simpa [prefixWord, tailWord_3293287, baseEnd_3293287] using wordTrace_append hprefix tailTrace_3293287
  have hstable : (prefixWord ++ tailWord_3293287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293287).length < 2 ^ (prefixWord ++ tailWord_3293287).sum := by decide
  have hdescent : baseEnd_3293287 < baseStart_3293287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293344 : List Nat := [2, 1, 1, 4, 2, 2, 3, 3, 1, 1, 3]
def baseStart_3293344 : Nat := 118140960795 + 3293344 * 2 ^ 59
def prefixEnd_3293344 : Nat := 4983230072969 + 3 ^ 40 * 3293344 * 2
def baseEnd_3293344 : Nat := 1691068432600868010154193

theorem tailTrace_3293344 : CollatzResearch.WordTrace tailWord_3293344 prefixEnd_3293344 1691068432600868010154193 := by
  unfold tailWord_3293344
  simp only [CollatzResearch.WordTrace]
  refine ⟨60059061890392310610355543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80078749187189747480474057 60059061890392310610355543)
  ·
    refine ⟨90088592835588465915533315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60059061890392310610355543 90088592835588465915533315)
    ·
      refine ⟨135132889253382698873299973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90088592835588465915533315 135132889253382698873299973)
      ·
        refine ⟨25337416735009256038743745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135132889253382698873299973 25337416735009256038743745)
        ·
          refine ⟨19003062551256942029057809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25337416735009256038743745 19003062551256942029057809)
          ·
            refine ⟨14252296913442706521793357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19003062551256942029057809 14252296913442706521793357)
            ·
              refine ⟨5344611342541014945672509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14252296913442706521793357 5344611342541014945672509)
              ·
                refine ⟨2004229253452880604627191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5344611342541014945672509 2004229253452880604627191)
                ·
                  refine ⟨3006343880179320906940787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2004229253452880604627191 3006343880179320906940787)
                  ·
                    refine ⟨4509515820268981360411181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3006343880179320906940787 4509515820268981360411181)
                    ·
                      refine ⟨1691068432600868010154193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4509515820268981360411181 1691068432600868010154193)
                      ·
                        rfl

theorem cell23_3293344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_3293344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293344 prefixEnd_3293344 := by exact prefixLift 3293344
  have htrace : WordTrace (prefixWord ++ tailWord_3293344) baseStart_3293344 baseEnd_3293344 := by
    simpa [prefixWord, tailWord_3293344, baseEnd_3293344] using wordTrace_append hprefix tailTrace_3293344
  have hstable : (prefixWord ++ tailWord_3293344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293344).length < 2 ^ (prefixWord ++ tailWord_3293344).sum := by decide
  have hdescent : baseEnd_3293344 < baseStart_3293344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293361 : List Nat := [1, 2, 2, 5, 3, 1, 1, 1, 3, 1, 3]
def baseStart_3293361 : Nat := 118140960795 + 3293361 * 2 ^ 59
def prefixEnd_3293361 : Nat := 4983230072969 + 3 ^ 40 * 3293361 * 2
def baseEnd_3293361 : Nat := 1691077161771994443641615

theorem tailTrace_3293361 : CollatzResearch.WordTrace tailWord_3293361 prefixEnd_3293361 1691077161771994443641615 := by
  unfold tailWord_3293361
  simp only [CollatzResearch.WordTrace]
  refine ⟨120118743821723033124079937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80079162547815355416053291 120118743821723033124079937)
  ·
    refine ⟨90089057866292274843059953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120118743821723033124079937 90089057866292274843059953)
    ·
      refine ⟨67566793399719206132294965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90089057866292274843059953 67566793399719206132294965)
      ·
        refine ⟨6334386881223675574902653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67566793399719206132294965 6334386881223675574902653)
        ·
          refine ⟨2375395080458878340588495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6334386881223675574902653 2375395080458878340588495)
          ·
            refine ⟨3563092620688317510882743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2375395080458878340588495 3563092620688317510882743)
            ·
              refine ⟨5344638931032476266324115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3563092620688317510882743 5344638931032476266324115)
              ·
                refine ⟨8016958396548714399486173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5344638931032476266324115 8016958396548714399486173)
                ·
                  refine ⟨3006359398705767899807315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8016958396548714399486173 3006359398705767899807315)
                  ·
                    refine ⟨4509539098058651849710973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3006359398705767899807315 4509539098058651849710973)
                    ·
                      refine ⟨1691077161771994443641615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4509539098058651849710973 1691077161771994443641615)
                      ·
                        rfl

theorem cell23_3293361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_3293361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293361 prefixEnd_3293361 := by exact prefixLift 3293361
  have htrace : WordTrace (prefixWord ++ tailWord_3293361) baseStart_3293361 baseEnd_3293361 := by
    simpa [prefixWord, tailWord_3293361, baseEnd_3293361] using wordTrace_append hprefix tailTrace_3293361
  have hstable : (prefixWord ++ tailWord_3293361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293361).length < 2 ^ (prefixWord ++ tailWord_3293361).sum := by decide
  have hdescent : baseEnd_3293361 < baseStart_3293361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293380 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_3293380 : Nat := 118140960795 + 3293380 * 2 ^ 59
def prefixEnd_3293380 : Nat := 4983230072969 + 3 ^ 40 * 3293380 * 2
def baseEnd_3293380 : Nat := 1691086917904429869304027

theorem tailTrace_3293380 : CollatzResearch.WordTrace tailWord_3293380 prefixEnd_3293380 1691086917904429869304027 := by
  unfold tailWord_3293380
  simp only [CollatzResearch.WordTrace]
  refine ⟨60059718404327099684510797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80079624539102799579347729 60059718404327099684510797)
  ·
    refine ⟨22522394401622662381691549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60059718404327099684510797 22522394401622662381691549)
    ·
      refine ⟨8445897900608498393134331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22522394401622662381691549 8445897900608498393134331)
      ·
        refine ⟨12668846850912747589701497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8445897900608498393134331 12668846850912747589701497)
        ·
          refine ⟨9501635138184560692276123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12668846850912747589701497 9501635138184560692276123)
          ·
            refine ⟨14252452707276841038414185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9501635138184560692276123 14252452707276841038414185)
            ·
              refine ⟨10689339530457630778810639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14252452707276841038414185 10689339530457630778810639)
              ·
                refine ⟨16034009295686446168215959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10689339530457630778810639 16034009295686446168215959)
                ·
                  refine ⟨24051013943529669252323939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16034009295686446168215959 24051013943529669252323939)
                  ·
                    refine ⟨36076520915294503878485909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24051013943529669252323939 36076520915294503878485909)
                    ·
                      refine ⟨1691086917904429869304027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36076520915294503878485909 1691086917904429869304027)
                      ·
                        rfl

theorem cell23_3293380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_3293380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293380 prefixEnd_3293380 := by exact prefixLift 3293380
  have htrace : WordTrace (prefixWord ++ tailWord_3293380) baseStart_3293380 baseEnd_3293380 := by
    simpa [prefixWord, tailWord_3293380, baseEnd_3293380] using wordTrace_append hprefix tailTrace_3293380
  have hstable : (prefixWord ++ tailWord_3293380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293380).length < 2 ^ (prefixWord ++ tailWord_3293380).sum := by decide
  have hdescent : baseEnd_3293380 < baseStart_3293380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293397 : List Nat := [1, 3, 2, 4, 2, 1, 1, 2, 1, 2, 4]
def baseStart_3293397 : Nat := 118140960795 + 3293397 * 2 ^ 59
def prefixEnd_3293397 : Nat := 4983230072969 + 3 ^ 40 * 3293397 * 2
def baseEnd_3293397 : Nat := 1691095647075556302791449

theorem tailTrace_3293397 : CollatzResearch.WordTrace tailWord_3293397 prefixEnd_3293397 1691095647075556302791449 := by
  unfold tailWord_3293397
  simp only [CollatzResearch.WordTrace]
  refine ⟨120120056849592611272390445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80080037899728407514926963 120120056849592611272390445)
  ·
    refine ⟨45045021318597229227146417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120120056849592611272390445 45045021318597229227146417)
    ·
      refine ⟨33783765988947921920359813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45045021318597229227146417 33783765988947921920359813)
      ·
        refine ⟨6334456122927735360067465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33783765988947921920359813 6334456122927735360067465)
        ·
          refine ⟨4750842092195801520050599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6334456122927735360067465 4750842092195801520050599)
          ·
            refine ⟨7126263138293702280075899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4750842092195801520050599 7126263138293702280075899)
            ·
              refine ⟨10689394707440553420113849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7126263138293702280075899 10689394707440553420113849)
              ·
                refine ⟨8017046030580415065085387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10689394707440553420113849 8017046030580415065085387)
                ·
                  refine ⟨12025569045870622597628081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8017046030580415065085387 12025569045870622597628081)
                  ·
                    refine ⟨9019176784402966948221061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12025569045870622597628081 9019176784402966948221061)
                    ·
                      refine ⟨1691095647075556302791449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9019176784402966948221061 1691095647075556302791449)
                      ·
                        rfl

theorem cell23_3293397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_3293397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293397 prefixEnd_3293397 := by exact prefixLift 3293397
  have htrace : WordTrace (prefixWord ++ tailWord_3293397) baseStart_3293397 baseEnd_3293397 := by
    simpa [prefixWord, tailWord_3293397, baseEnd_3293397] using wordTrace_append hprefix tailTrace_3293397
  have hstable : (prefixWord ++ tailWord_3293397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293397).length < 2 ^ (prefixWord ++ tailWord_3293397).sum := by decide
  have hdescent : baseEnd_3293397 < baseStart_3293397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293400 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 3, 3, 3]
def baseStart_3293400 : Nat := 118140960795 + 3293400 * 2 ^ 59
def prefixEnd_3293400 : Nat := 4983230072969 + 3 ^ 40 * 3293400 * 2
def baseEnd_3293400 : Nat := 1691097187517519791053935

theorem tailTrace_3293400 : CollatzResearch.WordTrace tailWord_3293400 prefixEnd_3293400 1691097187517519791053935 := by
  unfold tailWord_3293400
  simp only [CollatzResearch.WordTrace]
  refine ⟨60060083134290871392374827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80080110845721161856499769 60060083134290871392374827)
  ·
    refine ⟨90090124701436307088562241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60060083134290871392374827 90090124701436307088562241)
    ·
      refine ⟨67567593526077230316421681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90090124701436307088562241 67567593526077230316421681)
      ·
        refine ⟨50675695144557922737316261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67567593526077230316421681 50675695144557922737316261)
        ·
          refine ⟨9501692839604610513246799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50675695144557922737316261 9501692839604610513246799)
          ·
            refine ⟨14252539259406915769870199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9501692839604610513246799 14252539259406915769870199)
            ·
              refine ⟨21378808889110373654805299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14252539259406915769870199 21378808889110373654805299)
              ·
                refine ⟨32068213333665560482207949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21378808889110373654805299 32068213333665560482207949)
                ·
                  refine ⟨12025580000124585180827981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32068213333665560482207949 12025580000124585180827981)
                  ·
                    refine ⟨4509592500046719442810493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12025580000124585180827981 4509592500046719442810493)
                    ·
                      refine ⟨1691097187517519791053935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4509592500046719442810493 1691097187517519791053935)
                      ·
                        rfl

theorem cell23_3293400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_3293400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293400 prefixEnd_3293400 := by exact prefixLift 3293400
  have htrace : WordTrace (prefixWord ++ tailWord_3293400) baseStart_3293400 baseEnd_3293400 := by
    simpa [prefixWord, tailWord_3293400, baseEnd_3293400] using wordTrace_append hprefix tailTrace_3293400
  have hstable : (prefixWord ++ tailWord_3293400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293400).length < 2 ^ (prefixWord ++ tailWord_3293400).sum := by decide
  have hdescent : baseEnd_3293400 < baseStart_3293400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293457 : List Nat := [1, 2, 2, 1, 1, 5, 2, 2, 1, 4, 2]
def baseStart_3293457 : Nat := 118140960795 + 3293457 * 2 ^ 59
def prefixEnd_3293457 : Nat := 4983230072969 + 3 ^ 40 * 3293457 * 2
def baseEnd_3293457 : Nat := 1691126455914826068041173

theorem tailTrace_3293457 : CollatzResearch.WordTrace tailWord_3293457 prefixEnd_3293457 1691126455914826068041173 := by
  unfold tailWord_3293457
  simp only [CollatzResearch.WordTrace]
  refine ⟨120122245229375241519574625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80081496819583494346383083 120122245229375241519574625)
  ·
    refine ⟨90091683922031431139680969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120122245229375241519574625 90091683922031431139680969)
    ·
      refine ⟨67568762941523573354760727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90091683922031431139680969 67568762941523573354760727)
      ·
        refine ⟨101353144412285360032141091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67568762941523573354760727 101353144412285360032141091)
        ·
          refine ⟨152029716618428040048211637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101353144412285360032141091 152029716618428040048211637)
          ·
            refine ⟨14252785932977628754519841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152029716618428040048211637 14252785932977628754519841)
            ·
              refine ⟨10689589449733221565889881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14252785932977628754519841 10689589449733221565889881)
              ·
                refine ⟨8017192087299916174417411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10689589449733221565889881 8017192087299916174417411)
                ·
                  refine ⟨12025788130949874261626117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8017192087299916174417411 12025788130949874261626117)
                  ·
                    refine ⟨2254835274553101424054897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12025788130949874261626117 2254835274553101424054897)
                    ·
                      refine ⟨1691126455914826068041173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2254835274553101424054897 1691126455914826068041173)
                      ·
                        rfl

theorem cell23_3293457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 4, 2].length) (baseStart_3293457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293457 prefixEnd_3293457 := by exact prefixLift 3293457
  have htrace : WordTrace (prefixWord ++ tailWord_3293457) baseStart_3293457 baseEnd_3293457 := by
    simpa [prefixWord, tailWord_3293457, baseEnd_3293457] using wordTrace_append hprefix tailTrace_3293457
  have hstable : (prefixWord ++ tailWord_3293457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293457).length < 2 ^ (prefixWord ++ tailWord_3293457).sum := by decide
  have hdescent : baseEnd_3293457 < baseStart_3293457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293491 : List Nat := [1, 1, 1, 2, 5, 1, 5, 1, 2, 2, 2]
def baseStart_3293491 : Nat := 118140960795 + 3293491 * 2 ^ 59
def prefixEnd_3293491 : Nat := 4983230072969 + 3 ^ 40 * 3293491 * 2
def baseEnd_3293491 : Nat := 1691143914257078935016017

theorem tailTrace_3293491 : CollatzResearch.WordTrace tailWord_3293491 prefixEnd_3293491 1691143914257078935016017 := by
  unfold tailWord_3293491
  simp only [CollatzResearch.WordTrace]
  refine ⟨120123485311252065326312327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80082323540834710217541551 120123485311252065326312327)
  ·
    refine ⟨180185227966878097989468491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120123485311252065326312327 180185227966878097989468491)
    ·
      refine ⟨270277841950317146984202737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180185227966878097989468491 270277841950317146984202737)
      ·
        refine ⟨202708381462737860238152053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270277841950317146984202737 202708381462737860238152053)
        ·
          refine ⟨19003910762131674397326755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 202708381462737860238152053 19003910762131674397326755)
          ·
            refine ⟨28505866143197511595990133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19003910762131674397326755 28505866143197511595990133)
            ·
              refine ⟨2672424950924766712124075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28505866143197511595990133 2672424950924766712124075)
              ·
                refine ⟨4008637426387150068186113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2672424950924766712124075 4008637426387150068186113)
                ·
                  refine ⟨3006478069790362551139585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4008637426387150068186113 3006478069790362551139585)
                  ·
                    refine ⟨2254858552342771913354689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3006478069790362551139585 2254858552342771913354689)
                    ·
                      refine ⟨1691143914257078935016017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2254858552342771913354689 1691143914257078935016017)
                      ·
                        rfl

theorem cell23_3293491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 2, 2, 2].length) (baseStart_3293491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293491 prefixEnd_3293491 := by exact prefixLift 3293491
  have htrace : WordTrace (prefixWord ++ tailWord_3293491) baseStart_3293491 baseEnd_3293491 := by
    simpa [prefixWord, tailWord_3293491, baseEnd_3293491] using wordTrace_append hprefix tailTrace_3293491
  have hstable : (prefixWord ++ tailWord_3293491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293491).length < 2 ^ (prefixWord ++ tailWord_3293491).sum := by decide
  have hdescent : baseEnd_3293491 < baseStart_3293491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293591 : List Nat := [1, 1, 3, 3, 1, 1, 6, 2, 1, 4]
def baseStart_3293591 : Nat := 118140960795 + 3293591 * 2 ^ 59
def prefixEnd_3293591 : Nat := 4983230072969 + 3 ^ 40 * 3293591 * 2
def baseEnd_3293591 : Nat := 563731754107509514588519

theorem tailTrace_3293591 : CollatzResearch.WordTrace tailWord_3293591 prefixEnd_3293591 563731754107509514588519 := by
  unfold tailWord_3293591
  simp only [CollatzResearch.WordTrace]
  refine ⟨120127132610889782404952627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80084755073926521603301751 120127132610889782404952627)
  ·
    refine ⟨180190698916334673607428941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120127132610889782404952627 180190698916334673607428941)
    ·
      refine ⟨67571512093625502602785853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180190698916334673607428941 67571512093625502602785853)
      ·
        refine ⟨25339317035109563476044695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67571512093625502602785853 25339317035109563476044695)
        ·
          refine ⟨38008975552664345214067043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25339317035109563476044695 38008975552664345214067043)
          ·
            refine ⟨57013463328996517821100565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38008975552664345214067043 57013463328996517821100565)
            ·
              refine ⟨2672506093546711772864089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57013463328996517821100565 2672506093546711772864089)
              ·
                refine ⟨2004379570160033829648067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2672506093546711772864089 2004379570160033829648067)
                ·
                  refine ⟨3006569355240050744472101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2004379570160033829648067 3006569355240050744472101)
                  ·
                    refine ⟨563731754107509514588519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3006569355240050744472101 563731754107509514588519)
                    ·
                      rfl

theorem cell23_3293591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 1, 4].length) (baseStart_3293591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293591 prefixEnd_3293591 := by exact prefixLift 3293591
  have htrace : WordTrace (prefixWord ++ tailWord_3293591) baseStart_3293591 baseEnd_3293591 := by
    simpa [prefixWord, tailWord_3293591, baseEnd_3293591] using wordTrace_append hprefix tailTrace_3293591
  have hstable : (prefixWord ++ tailWord_3293591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293591).length < 2 ^ (prefixWord ++ tailWord_3293591).sum := by decide
  have hdescent : baseEnd_3293591 < baseStart_3293591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293617 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 3, 5]
def baseStart_3293617 : Nat := 118140960795 + 3293617 * 2 ^ 59
def prefixEnd_3293617 : Nat := 4983230072969 + 3 ^ 40 * 3293617 * 2
def baseEnd_3293617 : Nat := 563736204273181814013479

theorem tailTrace_3293617 : CollatzResearch.WordTrace tailWord_3293617 prefixEnd_3293617 563736204273181814013479 := by
  unfold tailWord_3293617
  simp only [CollatzResearch.WordTrace]
  refine ⟨120128080908795588845399105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80085387272530392563599403 120128080908795588845399105)
  ·
    refine ⟨90096060681596691634049329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120128080908795588845399105 90096060681596691634049329)
    ·
      refine ⟨67572045511197518725536997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90096060681596691634049329 67572045511197518725536997)
      ·
        refine ⟨12669758533349534761038187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67572045511197518725536997 12669758533349534761038187)
        ·
          refine ⟨19004637800024302141557281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12669758533349534761038187 19004637800024302141557281)
          ·
            refine ⟨14253478350018226606167961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19004637800024302141557281 14253478350018226606167961)
            ·
              refine ⟨10690108762513669954625971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14253478350018226606167961 10690108762513669954625971)
              ·
                refine ⟨16035163143770504931938957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10690108762513669954625971 16035163143770504931938957)
                ·
                  refine ⟨6013186178913939349477109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16035163143770504931938957 6013186178913939349477109)
                  ·
                    refine ⟨563736204273181814013479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6013186178913939349477109 563736204273181814013479)
                    ·
                      rfl

theorem cell23_3293617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_3293617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293617 prefixEnd_3293617 := by exact prefixLift 3293617
  have htrace : WordTrace (prefixWord ++ tailWord_3293617) baseStart_3293617 baseEnd_3293617 := by
    simpa [prefixWord, tailWord_3293617, baseEnd_3293617] using wordTrace_append hprefix tailTrace_3293617
  have hstable : (prefixWord ++ tailWord_3293617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293617).length < 2 ^ (prefixWord ++ tailWord_3293617).sum := by decide
  have hdescent : baseEnd_3293617 < baseStart_3293617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293637 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 3, 8, 2]
def baseStart_3293637 : Nat := 118140960795 + 3293637 * 2 ^ 59
def prefixEnd_3293637 : Nat := 4983230072969 + 3 ^ 40 * 3293637 * 2
def baseEnd_3293637 : Nat := 1691218882432635363790345

theorem tailTrace_3293637 : CollatzResearch.WordTrace tailWord_3293637 prefixEnd_3293637 1691218882432635363790345 := by
  unfold tailWord_3293637
  simp only [CollatzResearch.WordTrace]
  refine ⟨120128810368723132261127165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80085873579148754840751443 120128810368723132261127165)
  ·
    refine ⟨45048303888271174597922687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120128810368723132261127165 45048303888271174597922687)
    ·
      refine ⟨67572455832406761896884031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45048303888271174597922687 67572455832406761896884031)
      ·
        refine ⟨101358683748610142845326047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67572455832406761896884031 101358683748610142845326047)
        ·
          refine ⟨152038025622915214267989071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101358683748610142845326047 152038025622915214267989071)
          ·
            refine ⟨228057038434372821401983607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152038025622915214267989071 228057038434372821401983607)
            ·
              refine ⟨342085557651559232102975411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228057038434372821401983607 342085557651559232102975411)
              ·
                refine ⟨513128336477338848154463117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342085557651559232102975411 513128336477338848154463117)
                ·
                  refine ⟨192423126179002068057923669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 513128336477338848154463117 192423126179002068057923669)
                  ·
                    refine ⟨2254958509910180485053793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 192423126179002068057923669 2254958509910180485053793)
                    ·
                      refine ⟨1691218882432635363790345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2254958509910180485053793 1691218882432635363790345)
                      ·
                        rfl

theorem cell23_3293637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 8, 2].length) (baseStart_3293637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293637 prefixEnd_3293637 := by exact prefixLift 3293637
  have htrace : WordTrace (prefixWord ++ tailWord_3293637) baseStart_3293637 baseEnd_3293637 := by
    simpa [prefixWord, tailWord_3293637, baseEnd_3293637] using wordTrace_append hprefix tailTrace_3293637
  have hstable : (prefixWord ++ tailWord_3293637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293637).length < 2 ^ (prefixWord ++ tailWord_3293637).sum := by decide
  have hdescent : baseEnd_3293637 < baseStart_3293637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293657 : List Nat := [1, 2, 1, 2, 4, 1, 3, 2, 1, 1, 5]
def baseStart_3293657 : Nat := 118140960795 + 3293657 * 2 ^ 59
def prefixEnd_3293657 : Nat := 4983230072969 + 3 ^ 40 * 3293657 * 2
def baseEnd_3293657 : Nat := 1691229152045725285540253

theorem tailTrace_3293657 : CollatzResearch.WordTrace tailWord_3293657 prefixEnd_3293657 1691229152045725285540253 := by
  unfold tailWord_3293657
  simp only [CollatzResearch.WordTrace]
  refine ⟨120129539828650675676855225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80086359885767117117903483 120129539828650675676855225)
  ·
    refine ⟨90097154871488006757641419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120129539828650675676855225 90097154871488006757641419)
    ·
      refine ⟨135145732307232010136462129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90097154871488006757641419 135145732307232010136462129)
      ·
        refine ⟨101359299230424007602346597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135145732307232010136462129 101359299230424007602346597)
        ·
          refine ⟨19004868605704501425439987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101359299230424007602346597 19004868605704501425439987)
          ·
            refine ⟨28507302908556752138159981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19004868605704501425439987 28507302908556752138159981)
            ·
              refine ⟨10690238590708782051809993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28507302908556752138159981 10690238590708782051809993)
              ·
                refine ⟨8017678943031586538857495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10690238590708782051809993 8017678943031586538857495)
                ·
                  refine ⟨12026518414547379808286243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8017678943031586538857495 12026518414547379808286243)
                  ·
                    refine ⟨18039777621821069712429365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12026518414547379808286243 18039777621821069712429365)
                    ·
                      refine ⟨1691229152045725285540253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18039777621821069712429365 1691229152045725285540253)
                      ·
                        rfl

theorem cell23_3293657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_3293657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293657 prefixEnd_3293657 := by exact prefixLift 3293657
  have htrace : WordTrace (prefixWord ++ tailWord_3293657) baseStart_3293657 baseEnd_3293657 := by
    simpa [prefixWord, tailWord_3293657, baseEnd_3293657] using wordTrace_append hprefix tailTrace_3293657
  have hstable : (prefixWord ++ tailWord_3293657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293657).length < 2 ^ (prefixWord ++ tailWord_3293657).sum := by decide
  have hdescent : baseEnd_3293657 < baseStart_3293657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293671 : List Nat := [1, 1, 5, 2, 1, 1, 1, 4, 3, 2, 2]
def baseStart_3293671 : Nat := 118140960795 + 3293671 * 2 ^ 59
def prefixEnd_3293671 : Nat := 4983230072969 + 3 ^ 40 * 3293671 * 2
def baseEnd_3293671 : Nat := 1691236340774888230765189

theorem tailTrace_3293671 : CollatzResearch.WordTrace tailWord_3293671 prefixEnd_3293671 1691236340774888230765189 := by
  unfold tailWord_3293671
  simp only [CollatzResearch.WordTrace]
  refine ⟨120130050450599956067864867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80086700300399970711909911 120130050450599956067864867)
  ·
    refine ⟨180195075675899934101797301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120130050450599956067864867 180195075675899934101797301)
    ·
      refine ⟨16893288344615618822043497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180195075675899934101797301 16893288344615618822043497)
      ·
        refine ⟨12669966258461714116532623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16893288344615618822043497 12669966258461714116532623)
        ·
          refine ⟨19004949387692571174798935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12669966258461714116532623 19004949387692571174798935)
          ·
            refine ⟨28507424081538856762198403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19004949387692571174798935 28507424081538856762198403)
            ·
              refine ⟨42761136122308285143297605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28507424081538856762198403 42761136122308285143297605)
              ·
                refine ⟨8017713022932803464368301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42761136122308285143297605 8017713022932803464368301)
                ·
                  refine ⟨3006642383599801299138113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8017713022932803464368301 3006642383599801299138113)
                  ·
                    refine ⟨2254981787699850974353585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3006642383599801299138113 2254981787699850974353585)
                    ·
                      refine ⟨1691236340774888230765189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2254981787699850974353585 1691236340774888230765189)
                      ·
                        rfl

theorem cell23_3293671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_3293671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293671 prefixEnd_3293671 := by exact prefixLift 3293671
  have htrace : WordTrace (prefixWord ++ tailWord_3293671) baseStart_3293671 baseEnd_3293671 := by
    simpa [prefixWord, tailWord_3293671, baseEnd_3293671] using wordTrace_append hprefix tailTrace_3293671
  have hstable : (prefixWord ++ tailWord_3293671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293671).length < 2 ^ (prefixWord ++ tailWord_3293671).sum := by decide
  have hdescent : baseEnd_3293671 < baseStart_3293671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293682 : List Nat := [3, 2, 1, 4, 3, 1, 1, 3, 1, 1, 3]
def baseStart_3293682 : Nat := 118140960795 + 3293682 * 2 ^ 59
def prefixEnd_3293682 : Nat := 4983230072969 + 3 ^ 40 * 3293682 * 2
def baseEnd_3293682 : Nat := 1691241989062087687727639

theorem tailTrace_3293682 : CollatzResearch.WordTrace tailWord_3293682 prefixEnd_3293682 1691241989062087687727639 := by
  unfold tailWord_3293682
  simp only [CollatzResearch.WordTrace]
  refine ⟨30032612913390026236628825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80086967769040069964343533 30032612913390026236628825)
  ·
    refine ⟨22524459685042519677471619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30032612913390026236628825 22524459685042519677471619)
    ·
      refine ⟨33786689527563779516207429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22524459685042519677471619 33786689527563779516207429)
      ·
        refine ⟨6335004286418208659288893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33786689527563779516207429 6335004286418208659288893)
        ·
          refine ⟨2375626607406828247233335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6335004286418208659288893 2375626607406828247233335)
          ·
            refine ⟨3563439911110242370850003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2375626607406828247233335 3563439911110242370850003)
            ·
              refine ⟨5345159866665363556275005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3563439911110242370850003 5345159866665363556275005)
              ·
                refine ⟨2004434949999511333603127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5345159866665363556275005 2004434949999511333603127)
                ·
                  refine ⟨3006652424999267000404691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2004434949999511333603127 3006652424999267000404691)
                  ·
                    refine ⟨4509978637498900500607037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3006652424999267000404691 4509978637498900500607037)
                    ·
                      refine ⟨1691241989062087687727639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4509978637498900500607037 1691241989062087687727639)
                      ·
                        rfl

theorem cell23_3293682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_3293682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293682 prefixEnd_3293682 := by exact prefixLift 3293682
  have htrace : WordTrace (prefixWord ++ tailWord_3293682) baseStart_3293682 baseEnd_3293682 := by
    simpa [prefixWord, tailWord_3293682, baseEnd_3293682] using wordTrace_append hprefix tailTrace_3293682
  have hstable : (prefixWord ++ tailWord_3293682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293682).length < 2 ^ (prefixWord ++ tailWord_3293682).sum := by decide
  have hdescent : baseEnd_3293682 < baseStart_3293682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293731 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 3, 3, 2]
def baseStart_3293731 : Nat := 118140960795 + 3293731 * 2 ^ 59
def prefixEnd_3293731 : Nat := 4983230072969 + 3 ^ 40 * 3293731 * 2
def baseEnd_3293731 : Nat := 1691267149614157996014913

theorem tailTrace_3293731 : CollatzResearch.WordTrace tailWord_3293731 prefixEnd_3293731 1691267149614157996014913 := by
  unfold tailWord_3293731
  simp only [CollatzResearch.WordTrace]
  refine ⟨120132238830382586315049047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80088159220255057543366031 120132238830382586315049047)
  ·
    refine ⟨180198358245573879472573571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120132238830382586315049047 180198358245573879472573571)
    ·
      refine ⟨270297537368360819208860357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180198358245573879472573571 270297537368360819208860357)
      ·
        refine ⟨50680788256567653601661317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270297537368360819208860357 50680788256567653601661317)
        ·
          refine ⟨9502647798106435050311497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50680788256567653601661317 9502647798106435050311497)
          ·
            refine ⟨7126985848579826287733623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9502647798106435050311497 7126985848579826287733623)
            ·
              refine ⟨10690478772869739431600435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7126985848579826287733623 10690478772869739431600435)
              ·
                refine ⟨16035718159304609147400653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10690478772869739431600435 16035718159304609147400653)
                ·
                  refine ⟨6013394309739228430275245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16035718159304609147400653 6013394309739228430275245)
                  ·
                    refine ⟨2255022866152210661353217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6013394309739228430275245 2255022866152210661353217)
                    ·
                      refine ⟨1691267149614157996014913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2255022866152210661353217 1691267149614157996014913)
                      ·
                        rfl

theorem cell23_3293731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_3293731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293731 prefixEnd_3293731 := by exact prefixLift 3293731
  have htrace : WordTrace (prefixWord ++ tailWord_3293731) baseStart_3293731 baseEnd_3293731 := by
    simpa [prefixWord, tailWord_3293731, baseEnd_3293731] using wordTrace_append hprefix tailTrace_3293731
  have hstable : (prefixWord ++ tailWord_3293731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293731).length < 2 ^ (prefixWord ++ tailWord_3293731).sum := by decide
  have hdescent : baseEnd_3293731 < baseStart_3293731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293744 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 3, 4, 2]
def baseStart_3293744 : Nat := 118140960795 + 3293744 * 2 ^ 59
def prefixEnd_3293744 : Nat := 4983230072969 + 3 ^ 40 * 3293744 * 2
def baseEnd_3293744 : Nat := 1691273824862666445152353

theorem tailTrace_3293744 : CollatzResearch.WordTrace tailWord_3293744 prefixEnd_3293744 1691273824862666445152353 := by
  unfold tailWord_3293744
  simp only [CollatzResearch.WordTrace]
  refine ⟨60066356489667744767636143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80088475319556993023514857 60066356489667744767636143)
  ·
    refine ⟨90099534734501617151454215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60066356489667744767636143 90099534734501617151454215)
    ·
      refine ⟨135149302101752425727181323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90099534734501617151454215 135149302101752425727181323)
      ·
        refine ⟨202723953152628638590771985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135149302101752425727181323 202723953152628638590771985)
        ·
          refine ⟨152042964864471478943078989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202723953152628638590771985 152042964864471478943078989)
          ·
            refine ⟨57016111824176804603654621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152042964864471478943078989 57016111824176804603654621)
            ·
              refine ⟨21381041934066301726370483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57016111824176804603654621 21381041934066301726370483)
              ·
                refine ⟨32071562901099452589555725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21381041934066301726370483 32071562901099452589555725)
                ·
                  refine ⟨12026836087912294721083397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32071562901099452589555725 12026836087912294721083397)
                  ·
                    refine ⟨2255031766483555260203137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12026836087912294721083397 2255031766483555260203137)
                    ·
                      refine ⟨1691273824862666445152353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2255031766483555260203137 1691273824862666445152353)
                      ·
                        rfl

theorem cell23_3293744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3, 4, 2].length) (baseStart_3293744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293744 prefixEnd_3293744 := by exact prefixLift 3293744
  have htrace : WordTrace (prefixWord ++ tailWord_3293744) baseStart_3293744 baseEnd_3293744 := by
    simpa [prefixWord, tailWord_3293744, baseEnd_3293744] using wordTrace_append hprefix tailTrace_3293744
  have hstable : (prefixWord ++ tailWord_3293744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293744).length < 2 ^ (prefixWord ++ tailWord_3293744).sum := by decide
  have hdescent : baseEnd_3293744 < baseStart_3293744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293747 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 5]
def baseStart_3293747 : Nat := 118140960795 + 3293747 * 2 ^ 59
def prefixEnd_3293747 : Nat := 4983230072969 + 3 ^ 40 * 3293747 * 2
def baseEnd_3293747 : Nat := 1691275365304629933414839

theorem tailTrace_3293747 : CollatzResearch.WordTrace tailWord_3293747 prefixEnd_3293747 1691275365304629933414839 := by
  unfold tailWord_3293747
  simp only [CollatzResearch.WordTrace]
  refine ⟨120132822398324621047631495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80088548265549747365087663 120132822398324621047631495)
  ·
    refine ⟨180199233597486931571447243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120132822398324621047631495 180199233597486931571447243)
    ·
      refine ⟨270298850396230397357170865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180199233597486931571447243 270298850396230397357170865)
      ·
        refine ⟨202724137797172798017878149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270298850396230397357170865 202724137797172798017878149)
        ·
          refine ⟨38010775836969899628352153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202724137797172798017878149 38010775836969899628352153)
          ·
            refine ⟨28508081877727424721264115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38010775836969899628352153 28508081877727424721264115)
            ·
              refine ⟨42762122816591137081896173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28508081877727424721264115 42762122816591137081896173)
              ·
                refine ⟨16035796056221676405711065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42762122816591137081896173 16035796056221676405711065)
                ·
                  refine ⟨12026847042166257304283299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16035796056221676405711065 12026847042166257304283299)
                  ·
                    refine ⟨18040270563249385956424949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12026847042166257304283299 18040270563249385956424949)
                    ·
                      refine ⟨1691275365304629933414839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18040270563249385956424949 1691275365304629933414839)
                      ·
                        rfl

theorem cell23_3293747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_3293747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293747 prefixEnd_3293747 := by exact prefixLift 3293747
  have htrace : WordTrace (prefixWord ++ tailWord_3293747) baseStart_3293747 baseEnd_3293747 := by
    simpa [prefixWord, tailWord_3293747, baseEnd_3293747] using wordTrace_append hprefix tailTrace_3293747
  have hstable : (prefixWord ++ tailWord_3293747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293747).length < 2 ^ (prefixWord ++ tailWord_3293747).sum := by decide
  have hdescent : baseEnd_3293747 < baseStart_3293747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293778 : List Nat := [3, 2, 2, 1, 2, 1, 1, 5, 2, 2, 2]
def baseStart_3293778 : Nat := 118140960795 + 3293778 * 2 ^ 59
def prefixEnd_3293778 : Nat := 4983230072969 + 3 ^ 40 * 3293778 * 2
def baseEnd_3293778 : Nat := 1691291283204919312127197

theorem tailTrace_3293778 : CollatzResearch.WordTrace tailWord_3293778 prefixEnd_3293778 1691291283204919312127197 := by
  unfold tailWord_3293778
  simp only [CollatzResearch.WordTrace]
  refine ⟨30033488265303078335502497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80089302040808208894673325 30033488265303078335502497)
  ·
    refine ⟨22525116198977308751626873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30033488265303078335502497 22525116198977308751626873)
    ·
      refine ⟨16893837149232981563720155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22525116198977308751626873 16893837149232981563720155)
      ·
        refine ⟨25340755723849472345580233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16893837149232981563720155 25340755723849472345580233)
        ·
          refine ⟨19005566792887104259185175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25340755723849472345580233 19005566792887104259185175)
          ·
            refine ⟨28508350189330656388777763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19005566792887104259185175 28508350189330656388777763)
            ·
              refine ⟨42762525283995984583166645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28508350189330656388777763 42762525283995984583166645)
              ·
                refine ⟨4008986745374623554671873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42762525283995984583166645 4008986745374623554671873)
                ·
                  refine ⟨3006740059030967666003905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4008986745374623554671873 3006740059030967666003905)
                  ·
                    refine ⟨2255055044273225749502929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3006740059030967666003905 2255055044273225749502929)
                    ·
                      refine ⟨1691291283204919312127197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2255055044273225749502929 1691291283204919312127197)
                      ·
                        rfl

theorem cell23_3293778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_3293778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293778 prefixEnd_3293778 := by exact prefixLift 3293778
  have htrace : WordTrace (prefixWord ++ tailWord_3293778) baseStart_3293778 baseEnd_3293778 := by
    simpa [prefixWord, tailWord_3293778, baseEnd_3293778] using wordTrace_append hprefix tailTrace_3293778
  have hstable : (prefixWord ++ tailWord_3293778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293778).length < 2 ^ (prefixWord ++ tailWord_3293778).sum := by decide
  have hdescent : baseEnd_3293778 < baseStart_3293778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293807 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 5]
def baseStart_3293807 : Nat := 118140960795 + 3293807 * 2 ^ 59
def prefixEnd_3293807 : Nat := 4983230072969 + 3 ^ 40 * 3293807 * 2
def baseEnd_3293807 : Nat := 1691306174143899698664563

theorem tailTrace_3293807 : CollatzResearch.WordTrace tailWord_3293807 prefixEnd_3293807 1691306174143899698664563 := by
  unfold tailWord_3293807
  simp only [CollatzResearch.WordTrace]
  refine ⟨120135010778107251294815675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80090007185404834196543783 120135010778107251294815675)
  ·
    refine ⟨180202516167160876942223513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120135010778107251294815675 180202516167160876942223513)
    ·
      refine ⟨135151887125370657706667635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180202516167160876942223513 135151887125370657706667635)
      ·
        refine ⟨202727830688055986560001453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135151887125370657706667635 202727830688055986560001453)
        ·
          refine ⟨76022936508020994960000545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202727830688055986560001453 76022936508020994960000545)
          ·
            refine ⟨57017202381015746220000409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76022936508020994960000545 57017202381015746220000409)
            ·
              refine ⟨42762901785761809665000307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57017202381015746220000409 42762901785761809665000307)
              ·
                refine ⟨64144352678642714497500461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42762901785761809665000307 64144352678642714497500461)
                ·
                  refine ⟨24054132254491017936562673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64144352678642714497500461 24054132254491017936562673)
                  ·
                    refine ⟨18040599190868263452422005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24054132254491017936562673 18040599190868263452422005)
                    ·
                      refine ⟨1691306174143899698664563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18040599190868263452422005 1691306174143899698664563)
                      ·
                        rfl

theorem cell23_3293807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_3293807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293807 prefixEnd_3293807 := by exact prefixLift 3293807
  have htrace : WordTrace (prefixWord ++ tailWord_3293807) baseStart_3293807 baseEnd_3293807 := by
    simpa [prefixWord, tailWord_3293807, baseEnd_3293807] using wordTrace_append hprefix tailTrace_3293807
  have hstable : (prefixWord ++ tailWord_3293807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293807).length < 2 ^ (prefixWord ++ tailWord_3293807).sum := by decide
  have hdescent : baseEnd_3293807 < baseStart_3293807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293871 : List Nat := [1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 3]
def baseStart_3293871 : Nat := 118140960795 + 3293871 * 2 ^ 59
def prefixEnd_3293871 : Nat := 4983230072969 + 3 ^ 40 * 3293871 * 2
def baseEnd_3293871 : Nat := 1691339036905787448264269

theorem tailTrace_3293871 : CollatzResearch.WordTrace tailWord_3293871 prefixEnd_3293871 1691339036905787448264269 := by
  unfold tailWord_3293871
  simp only [CollatzResearch.WordTrace]
  refine ⟨120137345049875390225145467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80091563366583593483430311 120137345049875390225145467)
  ·
    refine ⟨180206017574813085337718201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120137345049875390225145467 180206017574813085337718201)
    ·
      refine ⟨135154513181109814003288651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180206017574813085337718201 135154513181109814003288651)
      ·
        refine ⟨202731769771664721004932977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135154513181109814003288651 202731769771664721004932977)
        ·
          refine ⟨152048827328748540753699733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202731769771664721004932977 152048827328748540753699733)
          ·
            refine ⟨7127288781035087847829675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152048827328748540753699733 7127288781035087847829675)
            ·
              refine ⟨10690933171552631771744513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7127288781035087847829675 10690933171552631771744513)
              ·
                refine ⟨8018199878664473828808385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10690933171552631771744513 8018199878664473828808385)
                ·
                  refine ⟨6013649908998355371606289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8018199878664473828808385 6013649908998355371606289)
                  ·
                    refine ⟨4510237431748766528704717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6013649908998355371606289 4510237431748766528704717)
                    ·
                      refine ⟨1691339036905787448264269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4510237431748766528704717 1691339036905787448264269)
                      ·
                        rfl

theorem cell23_3293871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 3].length) (baseStart_3293871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293871 prefixEnd_3293871 := by exact prefixLift 3293871
  have htrace : WordTrace (prefixWord ++ tailWord_3293871) baseStart_3293871 baseEnd_3293871 := by
    simpa [prefixWord, tailWord_3293871, baseEnd_3293871] using wordTrace_append hprefix tailTrace_3293871
  have hstable : (prefixWord ++ tailWord_3293871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293871).length < 2 ^ (prefixWord ++ tailWord_3293871).sum := by decide
  have hdescent : baseEnd_3293871 < baseStart_3293871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293874 : List Nat := [3, 2, 1, 1, 1, 2, 1, 6, 6]
def baseStart_3293874 : Nat := 118140960795 + 3293874 * 2 ^ 59
def prefixEnd_3293874 : Nat := 4983230072969 + 3 ^ 40 * 3293874 * 2
def baseEnd_3293874 : Nat := 187926730816416770725195

theorem tailTrace_3293874 : CollatzResearch.WordTrace tailWord_3293874 prefixEnd_3293874 187926730816416770725195 := by
  unfold tailWord_3293874
  simp only [CollatzResearch.WordTrace]
  refine ⟨30034363617216130434376169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80091636312576347825003117 30034363617216130434376169)
  ·
    refine ⟨22525772712912097825782127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30034363617216130434376169 22525772712912097825782127)
    ·
      refine ⟨33788659069368146738673191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22525772712912097825782127 33788659069368146738673191)
      ·
        refine ⟨50682988604052220108009787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33788659069368146738673191 50682988604052220108009787)
        ·
          refine ⟨76024482906078330162014681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50682988604052220108009787 76024482906078330162014681)
          ·
            refine ⟨57018362179558747621511011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76024482906078330162014681 57018362179558747621511011)
            ·
              refine ⟨85527543269338121432266517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57018362179558747621511011 85527543269338121432266517)
              ·
                refine ⟨4009103590750224442137493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85527543269338121432266517 4009103590750224442137493)
                ·
                  refine ⟨187926730816416770725195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4009103590750224442137493 187926730816416770725195)
                  ·
                    rfl

theorem cell23_3293874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_3293874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293874 prefixEnd_3293874 := by exact prefixLift 3293874
  have htrace : WordTrace (prefixWord ++ tailWord_3293874) baseStart_3293874 baseEnd_3293874 := by
    simpa [prefixWord, tailWord_3293874, baseEnd_3293874] using wordTrace_append hprefix tailTrace_3293874
  have hstable : (prefixWord ++ tailWord_3293874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293874).length < 2 ^ (prefixWord ++ tailWord_3293874).sum := by decide
  have hdescent : baseEnd_3293874 < baseStart_3293874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293935 : List Nat := [1, 1, 2, 1, 5, 3, 1, 4, 1, 1, 3]
def baseStart_3293935 : Nat := 118140960795 + 3293935 * 2 ^ 59
def prefixEnd_3293935 : Nat := 4983230072969 + 3 ^ 40 * 3293935 * 2
def baseEnd_3293935 : Nat := 1691371899667675197863975

theorem tailTrace_3293935 : CollatzResearch.WordTrace tailWord_3293935 prefixEnd_3293935 1691371899667675197863975 := by
  unfold tailWord_3293935
  simp only [CollatzResearch.WordTrace]
  refine ⟨120139679321643529155475259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80093119547762352770316839 120139679321643529155475259)
  ·
    refine ⟨180209518982465293733212889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120139679321643529155475259 180209518982465293733212889)
    ·
      refine ⟨135157139236848970299909667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180209518982465293733212889 135157139236848970299909667)
      ·
        refine ⟨202735708855273455449864501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135157139236848970299909667 202735708855273455449864501)
        ·
          refine ⟨19006472705181886448424797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 202735708855273455449864501 19006472705181886448424797)
          ·
            refine ⟨7127427264443207418159299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19006472705181886448424797 7127427264443207418159299)
            ·
              refine ⟨10691140896664811127238949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7127427264443207418159299 10691140896664811127238949)
              ·
                refine ⟨2004588918124652086357303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10691140896664811127238949 2004588918124652086357303)
                ·
                  refine ⟨3006883377186978129535955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2004588918124652086357303 3006883377186978129535955)
                  ·
                    refine ⟨4510325065780467194303933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3006883377186978129535955 4510325065780467194303933)
                    ·
                      refine ⟨1691371899667675197863975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4510325065780467194303933 1691371899667675197863975)
                      ·
                        rfl

theorem cell23_3293935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 1, 1, 3].length) (baseStart_3293935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293935 prefixEnd_3293935 := by exact prefixLift 3293935
  have htrace : WordTrace (prefixWord ++ tailWord_3293935) baseStart_3293935 baseEnd_3293935 := by
    simpa [prefixWord, tailWord_3293935, baseEnd_3293935] using wordTrace_append hprefix tailTrace_3293935
  have hstable : (prefixWord ++ tailWord_3293935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293935).length < 2 ^ (prefixWord ++ tailWord_3293935).sum := by decide
  have hdescent : baseEnd_3293935 < baseStart_3293935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293944 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 3, 1, 5]
def baseStart_3293944 : Nat := 118140960795 + 3293944 * 2 ^ 59
def prefixEnd_3293944 : Nat := 4983230072969 + 3 ^ 40 * 3293944 * 2
def baseEnd_3293944 : Nat := 1691376520993565662651433

theorem tailTrace_3293944 : CollatzResearch.WordTrace tailWord_3293944 prefixEnd_3293944 1691376520993565662651433 := by
  unfold tailWord_3293944
  simp only [CollatzResearch.WordTrace]
  refine ⟨60070003789305461846276443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80093338385740615795035257 60070003789305461846276443)
  ·
    refine ⟨90105005683958192769414665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60070003789305461846276443 90105005683958192769414665)
    ·
      refine ⟨67578754262968644577060999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90105005683958192769414665 67578754262968644577060999)
      ·
        refine ⟨101368131394452966865591499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67578754262968644577060999 101368131394452966865591499)
        ·
          refine ⟨152052197091679450298387249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101368131394452966865591499 152052197091679450298387249)
          ·
            refine ⟨114039147818759587723790437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152052197091679450298387249 114039147818759587723790437)
            ·
              refine ⟨21382340216017422698210707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114039147818759587723790437 21382340216017422698210707)
              ·
                refine ⟨32073510324026134047316061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21382340216017422698210707 32073510324026134047316061)
                ·
                  refine ⟨12027566371509800267743523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32073510324026134047316061 12027566371509800267743523)
                  ·
                    refine ⟨18041349557264700401615285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12027566371509800267743523 18041349557264700401615285)
                    ·
                      refine ⟨1691376520993565662651433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18041349557264700401615285 1691376520993565662651433)
                      ·
                        rfl

theorem cell23_3293944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_3293944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293944 prefixEnd_3293944 := by exact prefixLift 3293944
  have htrace : WordTrace (prefixWord ++ tailWord_3293944) baseStart_3293944 baseEnd_3293944 := by
    simpa [prefixWord, tailWord_3293944, baseEnd_3293944] using wordTrace_append hprefix tailTrace_3293944
  have hstable : (prefixWord ++ tailWord_3293944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293944).length < 2 ^ (prefixWord ++ tailWord_3293944).sum := by decide
  have hdescent : baseEnd_3293944 < baseStart_3293944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293961 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 3, 2, 3]
def baseStart_3293961 : Nat := 118140960795 + 3293961 * 2 ^ 59
def prefixEnd_3293961 : Nat := 4983230072969 + 3 ^ 40 * 3293961 * 2
def baseEnd_3293961 : Nat := 1691385250164692096138855

theorem tailTrace_3293961 : CollatzResearch.WordTrace tailWord_3293961 prefixEnd_3293961 1691385250164692096138855 := by
  unfold tailWord_3293961
  simp only [CollatzResearch.WordTrace]
  refine ⟨120140627619549335595921737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80093751746366223730614491 120140627619549335595921737)
  ·
    refine ⟨90105470714662001696941303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120140627619549335595921737 90105470714662001696941303)
    ·
      refine ⟨135158206071993002545411955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90105470714662001696941303 135158206071993002545411955)
      ·
        refine ⟨202737309107989503818117933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135158206071993002545411955 202737309107989503818117933)
        ·
          refine ⟨76026490915496063931794225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202737309107989503818117933 76026490915496063931794225)
          ·
            refine ⟨57019868186622047948845669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76026490915496063931794225 57019868186622047948845669)
            ·
              refine ⟨10691225284991633990408563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57019868186622047948845669 10691225284991633990408563)
              ·
                refine ⟨16036837927487450985612845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10691225284991633990408563 16036837927487450985612845)
                ·
                  refine ⟨6013814222807794119604817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16036837927487450985612845 6013814222807794119604817)
                  ·
                    refine ⟨4510360667105845589703613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6013814222807794119604817 4510360667105845589703613)
                    ·
                      refine ⟨1691385250164692096138855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4510360667105845589703613 1691385250164692096138855)
                      ·
                        rfl

theorem cell23_3293961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 2, 3].length) (baseStart_3293961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293961 prefixEnd_3293961 := by exact prefixLift 3293961
  have htrace : WordTrace (prefixWord ++ tailWord_3293961) baseStart_3293961 baseEnd_3293961 := by
    simpa [prefixWord, tailWord_3293961, baseEnd_3293961] using wordTrace_append hprefix tailTrace_3293961
  have hstable : (prefixWord ++ tailWord_3293961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293961).length < 2 ^ (prefixWord ++ tailWord_3293961).sum := by decide
  have hdescent : baseEnd_3293961 < baseStart_3293961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293978 : List Nat := [3, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3]
def baseStart_3293978 : Nat := 118140960795 + 3293978 * 2 ^ 59
def prefixEnd_3293978 : Nat := 4983230072969 + 3 ^ 40 * 3293978 * 2
def baseEnd_3293978 : Nat := 1691393979335818529626277

theorem tailTrace_3293978 : CollatzResearch.WordTrace tailWord_3293978 prefixEnd_3293978 1691393979335818529626277 := by
  unfold tailWord_3293978
  simp only [CollatzResearch.WordTrace]
  refine ⟨30035311915121936874822647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80094165106991831666193725 30035311915121936874822647)
  ·
    refine ⟨45052967872682905312233971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30035311915121936874822647 45052967872682905312233971)
    ·
      refine ⟨67579451809024357968350957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45052967872682905312233971 67579451809024357968350957)
      ·
        refine ⟨25342294428384134238131609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67579451809024357968350957 25342294428384134238131609)
        ·
          refine ⟨19006720821288100678598707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25342294428384134238131609 19006720821288100678598707)
          ·
            refine ⟨28510081231932151017898061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19006720821288100678598707 28510081231932151017898061)
            ·
              refine ⟨10691280461974556631711773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28510081231932151017898061 10691280461974556631711773)
              ·
                refine ⟨4009230173240458736891915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10691280461974556631711773 4009230173240458736891915)
                ·
                  refine ⟨6013845259860688105337873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4009230173240458736891915 6013845259860688105337873)
                  ·
                    refine ⟨4510383944895516079003405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6013845259860688105337873 4510383944895516079003405)
                    ·
                      refine ⟨1691393979335818529626277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4510383944895516079003405 1691393979335818529626277)
                      ·
                        rfl

theorem cell23_3293978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_3293978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293978 prefixEnd_3293978 := by exact prefixLift 3293978
  have htrace : WordTrace (prefixWord ++ tailWord_3293978) baseStart_3293978 baseEnd_3293978 := by
    simpa [prefixWord, tailWord_3293978, baseEnd_3293978] using wordTrace_append hprefix tailTrace_3293978
  have hstable : (prefixWord ++ tailWord_3293978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293978).length < 2 ^ (prefixWord ++ tailWord_3293978).sum := by decide
  have hdescent : baseEnd_3293978 < baseStart_3293978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293992 : List Nat := [2, 1, 5, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_3293992 : Nat := 118140960795 + 3293992 * 2 ^ 59
def prefixEnd_3293992 : Nat := 4983230072969 + 3 ^ 40 * 3293992 * 2
def baseEnd_3293992 : Nat := 1691401168064981474851213

theorem tailTrace_3293992 : CollatzResearch.WordTrace tailWord_3293992 prefixEnd_3293992 1691401168064981474851213 := by
  unfold tailWord_3293992
  simp only [CollatzResearch.WordTrace]
  refine ⟨60070879141218513945150115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80094505521624685260200153 60070879141218513945150115)
  ·
    refine ⟨90106318711827770917725173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60070879141218513945150115 90106318711827770917725173)
    ·
      refine ⟨8447467379233853523536735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90106318711827770917725173 8447467379233853523536735)
      ·
        refine ⟨12671201068850780285305103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8447467379233853523536735 12671201068850780285305103)
        ·
          refine ⟨19006801603276170427957655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12671201068850780285305103 19006801603276170427957655)
          ·
            refine ⟨28510202404914255641936483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19006801603276170427957655 28510202404914255641936483)
            ·
              refine ⟨42765303607371383462904725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28510202404914255641936483 42765303607371383462904725)
              ·
                refine ⟨2004623606595533599823659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42765303607371383462904725 2004623606595533599823659)
                ·
                  refine ⟨3006935409893300399735489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2004623606595533599823659 3006935409893300399735489)
                  ·
                    refine ⟨2255201557419975299801617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3006935409893300399735489 2255201557419975299801617)
                    ·
                      refine ⟨1691401168064981474851213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2255201557419975299801617 1691401168064981474851213)
                      ·
                        rfl

theorem cell23_3293992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_3293992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3293992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3293992 prefixEnd_3293992 := by exact prefixLift 3293992
  have htrace : WordTrace (prefixWord ++ tailWord_3293992) baseStart_3293992 baseEnd_3293992 := by
    simpa [prefixWord, tailWord_3293992, baseEnd_3293992] using wordTrace_append hprefix tailTrace_3293992
  have hstable : (prefixWord ++ tailWord_3293992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293992).length < 2 ^ (prefixWord ++ tailWord_3293992).sum := by decide
  have hdescent : baseEnd_3293992 < baseStart_3293992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294061 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_3294061 : Nat := 118140960795 + 3294061 * 2 ^ 59
def prefixEnd_3294061 : Nat := 4983230072969 + 3 ^ 40 * 3294061 * 2
def baseEnd_3294061 : Nat := 1691436598230141704888395

theorem tailTrace_3294061 : CollatzResearch.WordTrace tailWord_3294061 prefixEnd_3294061 1691436598230141704888395 := by
  unfold tailWord_3294061
  simp only [CollatzResearch.WordTrace]
  refine ⟨120144274919187052674562037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80096183279458035116374691 120144274919187052674562037)
  ·
    refine ⟨11263525773673786188240191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120144274919187052674562037 11263525773673786188240191)
    ·
      refine ⟨16895288660510679282360287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11263525773673786188240191 16895288660510679282360287)
      ·
        refine ⟨25342932990766018923540431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16895288660510679282360287 25342932990766018923540431)
        ·
          refine ⟨38014399486149028385310647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25342932990766018923540431 38014399486149028385310647)
          ·
            refine ⟨57021599229223542577965971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38014399486149028385310647 57021599229223542577965971)
            ·
              refine ⟨85532398843835313866948957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57021599229223542577965971 85532398843835313866948957)
              ·
                refine ⟨32074649566438242700105859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85532398843835313866948957 32074649566438242700105859)
                ·
                  refine ⟨48111974349657364050158789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32074649566438242700105859 48111974349657364050158789)
                  ·
                    refine ⟨9020995190560755759404773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48111974349657364050158789 9020995190560755759404773)
                    ·
                      refine ⟨1691436598230141704888395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9020995190560755759404773 1691436598230141704888395)
                      ·
                        rfl

theorem cell23_3294061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_3294061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294061 prefixEnd_3294061 := by exact prefixLift 3294061
  have htrace : WordTrace (prefixWord ++ tailWord_3294061) baseStart_3294061 baseEnd_3294061 := by
    simpa [prefixWord, tailWord_3294061, baseEnd_3294061] using wordTrace_append hprefix tailTrace_3294061
  have hstable : (prefixWord ++ tailWord_3294061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294061).length < 2 ^ (prefixWord ++ tailWord_3294061).sum := by decide
  have hdescent : baseEnd_3294061 < baseStart_3294061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294102 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_3294102 : Nat := 118140960795 + 3294102 * 2 ^ 59
def prefixEnd_3294102 : Nat := 4983230072969 + 3 ^ 40 * 3294102 * 2
def baseEnd_3294102 : Nat := 1691457650936976044475707

theorem tailTrace_3294102 : CollatzResearch.WordTrace tailWord_3294102 prefixEnd_3294102 1691457650936976044475707 := by
  unfold tailWord_3294102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7509110644502407292300285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80097180208025677784536373 7509110644502407292300285)
  ·
    refine ⟨2815916491688402734612607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7509110644502407292300285 2815916491688402734612607)
    ·
      refine ⟨4223874737532604101918911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2815916491688402734612607 4223874737532604101918911)
      ·
        refine ⟨6335812106298906152878367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4223874737532604101918911 6335812106298906152878367)
        ·
          refine ⟨9503718159448359229317551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6335812106298906152878367 9503718159448359229317551)
          ·
            refine ⟨14255577239172538843976327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9503718159448359229317551 14255577239172538843976327)
            ·
              refine ⟨21383365858758808265964491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14255577239172538843976327 21383365858758808265964491)
              ·
                refine ⟨32075048788138212398946737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21383365858758808265964491 32075048788138212398946737)
                ·
                  refine ⟨24056286591103659299210053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32075048788138212398946737 24056286591103659299210053)
                  ·
                    refine ⟨4510553735831936118601885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24056286591103659299210053 4510553735831936118601885)
                    ·
                      refine ⟨1691457650936976044475707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4510553735831936118601885 1691457650936976044475707)
                      ·
                        rfl

theorem cell23_3294102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_3294102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294102 prefixEnd_3294102 := by exact prefixLift 3294102
  have htrace : WordTrace (prefixWord ++ tailWord_3294102) baseStart_3294102 baseEnd_3294102 := by
    simpa [prefixWord, tailWord_3294102, baseEnd_3294102] using wordTrace_append hprefix tailTrace_3294102
  have hstable : (prefixWord ++ tailWord_3294102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294102).length < 2 ^ (prefixWord ++ tailWord_3294102).sum := by decide
  have hdescent : baseEnd_3294102 < baseStart_3294102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294121 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 1, 3, 4]
def baseStart_3294121 : Nat := 118140960795 + 3294121 * 2 ^ 59
def prefixEnd_3294121 : Nat := 4983230072969 + 3 ^ 40 * 3294121 * 2
def baseEnd_3294121 : Nat := 1691467407069411470138119

theorem tailTrace_3294121 : CollatzResearch.WordTrace tailWord_3294121 prefixEnd_3294121 1691467407069411470138119 := by
  unfold tailWord_3294121
  simp only [CollatzResearch.WordTrace]
  refine ⟨120146463298969682921746217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80097642199313121947830811 120146463298969682921746217)
  ·
    refine ⟨90109847474227262191309663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120146463298969682921746217 90109847474227262191309663)
    ·
      refine ⟨135164771211340893286964495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90109847474227262191309663 135164771211340893286964495)
      ·
        refine ⟨202747156817011339930446743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135164771211340893286964495 202747156817011339930446743)
        ·
          refine ⟨304120735225517009895670115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202747156817011339930446743 304120735225517009895670115)
          ·
            refine ⟨456181102838275514843505173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304120735225517009895670115 456181102838275514843505173)
            ·
              refine ⟨21383489195544164758289305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 456181102838275514843505173 21383489195544164758289305)
              ·
                refine ⟨16037616896658123568716979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21383489195544164758289305 16037616896658123568716979)
                ·
                  refine ⟨24056425344987185353075469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16037616896658123568716979 24056425344987185353075469)
                  ·
                    refine ⟨9021159504370194507403301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24056425344987185353075469 9021159504370194507403301)
                    ·
                      refine ⟨1691467407069411470138119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9021159504370194507403301 1691467407069411470138119)
                      ·
                        rfl

theorem cell23_3294121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_3294121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294121 prefixEnd_3294121 := by exact prefixLift 3294121
  have htrace : WordTrace (prefixWord ++ tailWord_3294121) baseStart_3294121 baseEnd_3294121 := by
    simpa [prefixWord, tailWord_3294121, baseEnd_3294121] using wordTrace_append hprefix tailTrace_3294121
  have hstable : (prefixWord ++ tailWord_3294121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294121).length < 2 ^ (prefixWord ++ tailWord_3294121).sum := by decide
  have hdescent : baseEnd_3294121 < baseStart_3294121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294138 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2]
def baseStart_3294138 : Nat := 118140960795 + 3294138 * 2 ^ 59
def prefixEnd_3294138 : Nat := 4983230072969 + 3 ^ 40 * 3294138 * 2
def baseEnd_3294138 : Nat := 1691476136240537903625541

theorem tailTrace_3294138 : CollatzResearch.WordTrace tailWord_3294138 prefixEnd_3294138 1691476136240537903625541 := by
  unfold tailWord_3294138
  simp only [CollatzResearch.WordTrace]
  refine ⟨30036770834977023706278767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80098055559938729883410045 30036770834977023706278767)
  ·
    refine ⟨45055156252465535559418151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30036770834977023706278767 45055156252465535559418151)
    ·
      refine ⟨67582734378698303339127227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45055156252465535559418151 67582734378698303339127227)
      ·
        refine ⟨101374101568047455008690841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67582734378698303339127227 101374101568047455008690841)
        ·
          refine ⟨76030576176035591256518131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101374101568047455008690841 76030576176035591256518131)
          ·
            refine ⟨114045864264053386884777197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76030576176035591256518131 114045864264053386884777197)
            ·
              refine ⟨42767199099020020081791449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114045864264053386884777197 42767199099020020081791449)
              ·
                refine ⟨32075399324265015061343587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42767199099020020081791449 32075399324265015061343587)
                ·
                  refine ⟨48113098986397522592015381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32075399324265015061343587 48113098986397522592015381)
                  ·
                    refine ⟨2255301514987383871500721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48113098986397522592015381 2255301514987383871500721)
                    ·
                      refine ⟨1691476136240537903625541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2255301514987383871500721 1691476136240537903625541)
                      ·
                        rfl

theorem cell23_3294138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2].length) (baseStart_3294138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294138 prefixEnd_3294138 := by exact prefixLift 3294138
  have htrace : WordTrace (prefixWord ++ tailWord_3294138) baseStart_3294138 baseEnd_3294138 := by
    simpa [prefixWord, tailWord_3294138, baseEnd_3294138] using wordTrace_append hprefix tailTrace_3294138
  have hstable : (prefixWord ++ tailWord_3294138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294138).length < 2 ^ (prefixWord ++ tailWord_3294138).sum := by decide
  have hdescent : baseEnd_3294138 < baseStart_3294138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294151 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_3294151 : Nat := 118140960795 + 3294151 * 2 ^ 59
def prefixEnd_3294151 : Nat := 4983230072969 + 3 ^ 40 * 3294151 * 2
def baseEnd_3294151 : Nat := 1691482811489046352762981

theorem tailTrace_3294151 : CollatzResearch.WordTrace tailWord_3294151 prefixEnd_3294151 1691482811489046352762981 := by
  unfold tailWord_3294151
  simp only [CollatzResearch.WordTrace]
  refine ⟨120147557488860998045338307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80098371659240665363558871 120147557488860998045338307)
  ·
    refine ⟨180221336233291497068007461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120147557488860998045338307 180221336233291497068007461)
    ·
      refine ⟨33791500543742155700251399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180221336233291497068007461 33791500543742155700251399)
      ·
        refine ⟨50687250815613233550377099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33791500543742155700251399 50687250815613233550377099)
        ·
          refine ⟨76030876223419850325565649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50687250815613233550377099 76030876223419850325565649)
          ·
            refine ⟨57023157167564887744174237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76030876223419850325565649 57023157167564887744174237)
            ·
              refine ⟨21383683937836832904065339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57023157167564887744174237 21383683937836832904065339)
              ·
                refine ⟨32075525906755249356098009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21383683937836832904065339 32075525906755249356098009)
                ·
                  refine ⟨24056644430066437017073507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32075525906755249356098009 24056644430066437017073507)
                  ·
                    refine ⟨36084966645099655525610261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24056644430066437017073507 36084966645099655525610261)
                    ·
                      refine ⟨1691482811489046352762981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36084966645099655525610261 1691482811489046352762981)
                      ·
                        rfl

theorem cell23_3294151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_3294151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294151 prefixEnd_3294151 := by exact prefixLift 3294151
  have htrace : WordTrace (prefixWord ++ tailWord_3294151) baseStart_3294151 baseEnd_3294151 := by
    simpa [prefixWord, tailWord_3294151, baseEnd_3294151] using wordTrace_append hprefix tailTrace_3294151
  have hstable : (prefixWord ++ tailWord_3294151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294151).length < 2 ^ (prefixWord ++ tailWord_3294151).sum := by decide
  have hdescent : baseEnd_3294151 < baseStart_3294151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294161 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 8]
def baseStart_3294161 : Nat := 118140960795 + 3294161 * 2 ^ 59
def prefixEnd_3294161 : Nat := 4983230072969 + 3 ^ 40 * 3294161 * 2
def baseEnd_3294161 : Nat := 187943105143954590404215

theorem tailTrace_3294161 : CollatzResearch.WordTrace tailWord_3294161 prefixEnd_3294161 187943105143954590404215 := by
  unfold tailWord_3294161
  simp only [CollatzResearch.WordTrace]
  refine ⟨120147922218824769753202337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80098614812549846502134891 120147922218824769753202337)
  ·
    refine ⟨90110941664118577314901753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120147922218824769753202337 90110941664118577314901753)
    ·
      refine ⟨67583206248088932986176315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90110941664118577314901753 67583206248088932986176315)
      ·
        refine ⟨101374809372133399479264473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67583206248088932986176315 101374809372133399479264473)
        ·
          refine ⟨76031107029100049609448355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101374809372133399479264473 76031107029100049609448355)
          ·
            refine ⟨114046660543650074414172533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76031107029100049609448355 114046660543650074414172533)
            ·
              refine ⟨10691874425967194476328675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114046660543650074414172533 10691874425967194476328675)
              ·
                refine ⟨16037811638950791714493013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10691874425967194476328675 16037811638950791714493013)
                ·
                  refine ⟨187943105143954590404215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16037811638950791714493013 187943105143954590404215)
                  ·
                    rfl

theorem cell23_3294161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 8].length) (baseStart_3294161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294161 prefixEnd_3294161 := by exact prefixLift 3294161
  have htrace : WordTrace (prefixWord ++ tailWord_3294161) baseStart_3294161 baseEnd_3294161 := by
    simpa [prefixWord, tailWord_3294161, baseEnd_3294161] using wordTrace_append hprefix tailTrace_3294161
  have hstable : (prefixWord ++ tailWord_3294161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294161).length < 2 ^ (prefixWord ++ tailWord_3294161).sum := by decide
  have hdescent : baseEnd_3294161 < baseStart_3294161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294222 : List Nat := [4, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3]
def baseStart_3294222 : Nat := 118140960795 + 3294222 * 2 ^ 59
def prefixEnd_3294222 : Nat := 4983230072969 + 3 ^ 40 * 3294222 * 2
def baseEnd_3294222 : Nat := 1691519268615515574975155

theorem tailTrace_3294222 : CollatzResearch.WordTrace tailWord_3294222 prefixEnd_3294222 1691519268615515574975155 := by
  unfold tailWord_3294222
  simp only [CollatzResearch.WordTrace]
  refine ⟨15018768383950472146396615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80100098047735851447448613 15018768383950472146396615)
  ·
    refine ⟨22528152575925708219594923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15018768383950472146396615 22528152575925708219594923)
    ·
      refine ⟨33792228863888562329392385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22528152575925708219594923 33792228863888562329392385)
      ·
        refine ⟨25344171647916421747044289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33792228863888562329392385 25344171647916421747044289)
        ·
          refine ⟨19008128735937316310283217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25344171647916421747044289 19008128735937316310283217)
          ·
            refine ⟨14256096551952987232712413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19008128735937316310283217 14256096551952987232712413)
            ·
              refine ⟨5346036206982370212267155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14256096551952987232712413 5346036206982370212267155)
              ·
                refine ⟨8019054310473555318400733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5346036206982370212267155 8019054310473555318400733)
                ·
                  refine ⟨3007145366427583244400275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8019054310473555318400733 3007145366427583244400275)
                  ·
                    refine ⟨4510718049641374866600413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3007145366427583244400275 4510718049641374866600413)
                    ·
                      refine ⟨1691519268615515574975155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4510718049641374866600413 1691519268615515574975155)
                      ·
                        rfl

theorem cell23_3294222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_3294222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294222 prefixEnd_3294222 := by exact prefixLift 3294222
  have htrace : WordTrace (prefixWord ++ tailWord_3294222) baseStart_3294222 baseEnd_3294222 := by
    simpa [prefixWord, tailWord_3294222, baseEnd_3294222] using wordTrace_append hprefix tailTrace_3294222
  have hstable : (prefixWord ++ tailWord_3294222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294222).length < 2 ^ (prefixWord ++ tailWord_3294222).sum := by decide
  have hdescent : baseEnd_3294222 < baseStart_3294222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294242 : List Nat := [3, 3, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_3294242 : Nat := 118140960795 + 3294242 * 2 ^ 59
def prefixEnd_3294242 : Nat := 4983230072969 + 3 ^ 40 * 3294242 * 2
def baseEnd_3294242 : Nat := 563843179409535165575021

theorem tailTrace_3294242 : CollatzResearch.WordTrace tailWord_3294242 prefixEnd_3294242 563843179409535165575021 := by
  unfold tailWord_3294242
  simp only [CollatzResearch.WordTrace]
  refine ⟨30037719132882830146725245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80100584354354213724600653 30037719132882830146725245)
  ·
    refine ⟨11264144674831061305021967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30037719132882830146725245 11264144674831061305021967)
    ·
      refine ⟨16896217012246591957532951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11264144674831061305021967 16896217012246591957532951)
      ·
        refine ⟨25344325518369887936299427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16896217012246591957532951 25344325518369887936299427)
        ·
          refine ⟨38016488277554831904449141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25344325518369887936299427 38016488277554831904449141)
          ·
            refine ⟨3564045776020765491042107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38016488277554831904449141 3564045776020765491042107)
            ·
              refine ⟨5346068664031148236563161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3564045776020765491042107 5346068664031148236563161)
              ·
                refine ⟨4009551498023361177422371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5346068664031148236563161 4009551498023361177422371)
                ·
                  refine ⟨6014327247035041766133557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4009551498023361177422371 6014327247035041766133557)
                  ·
                    refine ⟨563843179409535165575021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6014327247035041766133557 563843179409535165575021)
                    ·
                      rfl

theorem cell23_3294242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_3294242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294242 prefixEnd_3294242 := by exact prefixLift 3294242
  have htrace : WordTrace (prefixWord ++ tailWord_3294242) baseStart_3294242 baseEnd_3294242 := by
    simpa [prefixWord, tailWord_3294242, baseEnd_3294242] using wordTrace_append hprefix tailTrace_3294242
  have hstable : (prefixWord ++ tailWord_3294242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294242).length < 2 ^ (prefixWord ++ tailWord_3294242).sum := by decide
  have hdescent : baseEnd_3294242 < baseStart_3294242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294251 : List Nat := [1, 1, 1, 1, 2, 1, 5, 11]
def baseStart_3294251 : Nat := 118140960795 + 3294251 * 2 ^ 59
def prefixEnd_3294251 : Nat := 4983230072969 + 3 ^ 40 * 3294251 * 2
def baseEnd_3294251 : Nat := 62649413316833183759723

theorem tailTrace_3294251 : CollatzResearch.WordTrace tailWord_3294251 prefixEnd_3294251 62649413316833183759723 := by
  unfold tailWord_3294251
  simp only [CollatzResearch.WordTrace]
  refine ⟨120151204788498715123978607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80100803192332476749319071 120151204788498715123978607)
  ·
    refine ⟨180226807182748072685967911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120151204788498715123978607 180226807182748072685967911)
    ·
      refine ⟨270340210774122109028951867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180226807182748072685967911 270340210774122109028951867)
      ·
        refine ⟨405510316161183163543427801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270340210774122109028951867 405510316161183163543427801)
        ·
          refine ⟨304132737120887372657570851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405510316161183163543427801 304132737120887372657570851)
          ·
            refine ⟨456199105681331058986356277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304132737120887372657570851 456199105681331058986356277)
            ·
              refine ⟨42768666157624786779970901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 456199105681331058986356277 42768666157624786779970901)
              ·
                refine ⟨62649413316833183759723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 42768666157624786779970901 62649413316833183759723)
                ·
                  rfl

theorem cell23_3294251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 11].length) (baseStart_3294251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294251 prefixEnd_3294251 := by exact prefixLift 3294251
  have htrace : WordTrace (prefixWord ++ tailWord_3294251) baseStart_3294251 baseEnd_3294251 := by
    simpa [prefixWord, tailWord_3294251, baseEnd_3294251] using wordTrace_append hprefix tailTrace_3294251
  have hstable : (prefixWord ++ tailWord_3294251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294251).length < 2 ^ (prefixWord ++ tailWord_3294251).sum := by decide
  have hdescent : baseEnd_3294251 < baseStart_3294251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294265 : List Nat := [1, 2, 1, 5, 2, 1, 3, 1, 1, 1, 5]
def baseStart_3294265 : Nat := 118140960795 + 3294265 * 2 ^ 59
def prefixEnd_3294265 : Nat := 4983230072969 + 3 ^ 40 * 3294265 * 2
def baseEnd_3294265 : Nat := 1691541348283658906737457

theorem tailTrace_3294265 : CollatzResearch.WordTrace tailWord_3294265 prefixEnd_3294265 1691541348283658906737457 := by
  unfold tailWord_3294265
  simp only [CollatzResearch.WordTrace]
  refine ⟨120151715410447995514988249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80101143606965330343325499 120151715410447995514988249)
  ·
    refine ⟨90113786557835996636241187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120151715410447995514988249 90113786557835996636241187)
    ·
      refine ⟨135170679836753994954361781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90113786557835996636241187 135170679836753994954361781)
      ·
        refine ⟨12672251234695687026971417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135170679836753994954361781 12672251234695687026971417)
        ·
          refine ⟨9504188426021765270228563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12672251234695687026971417 9504188426021765270228563)
          ·
            refine ⟨14256282639032647905342845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9504188426021765270228563 14256282639032647905342845)
            ·
              refine ⟨5346105989637242964503567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14256282639032647905342845 5346105989637242964503567)
              ·
                refine ⟨8019158984455864446755351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5346105989637242964503567 8019158984455864446755351)
                ·
                  refine ⟨12028738476683796670133027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8019158984455864446755351 12028738476683796670133027)
                  ·
                    refine ⟨18043107715025695005199541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12028738476683796670133027 18043107715025695005199541)
                    ·
                      refine ⟨1691541348283658906737457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18043107715025695005199541 1691541348283658906737457)
                      ·
                        rfl

theorem cell23_3294265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_3294265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294265 prefixEnd_3294265 := by exact prefixLift 3294265
  have htrace : WordTrace (prefixWord ++ tailWord_3294265) baseStart_3294265 baseEnd_3294265 := by
    simpa [prefixWord, tailWord_3294265, baseEnd_3294265] using wordTrace_append hprefix tailTrace_3294265
  have hstable : (prefixWord ++ tailWord_3294265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294265).length < 2 ^ (prefixWord ++ tailWord_3294265).sum := by decide
  have hdescent : baseEnd_3294265 < baseStart_3294265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294273 : List Nat := [1, 2, 5, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_3294273 : Nat := 118140960795 + 3294273 * 2 ^ 59
def prefixEnd_3294273 : Nat := 4983230072969 + 3 ^ 40 * 3294273 * 2
def baseEnd_3294273 : Nat := 1691545456128894875437421

theorem tailTrace_3294273 : CollatzResearch.WordTrace tailWord_3294273 prefixEnd_3294273 1691545456128894875437421 := by
  unfold tailWord_3294273
  simp only [CollatzResearch.WordTrace]
  refine ⟨120152007194419012881279473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80101338129612675254186315 120152007194419012881279473)
  ·
    refine ⟨90114005395814259660959605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120152007194419012881279473 90114005395814259660959605)
    ·
      refine ⟨8448188005857586843214963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90114005395814259660959605 8448188005857586843214963)
      ·
        refine ⟨12672282008786380264822445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8448188005857586843214963 12672282008786380264822445)
        ·
          refine ⟨4752105753294892599308417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12672282008786380264822445 4752105753294892599308417)
          ·
            refine ⟨3564079314971169449481313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4752105753294892599308417 3564079314971169449481313)
            ·
              refine ⟨2673059486228377087110985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3564079314971169449481313 2673059486228377087110985)
              ·
                refine ⟨2004794614671282815333239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2673059486228377087110985 2004794614671282815333239)
                ·
                  refine ⟨3007191922006924222999859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2004794614671282815333239 3007191922006924222999859)
                  ·
                    refine ⟨4510787883010386334499789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3007191922006924222999859 4510787883010386334499789)
                    ·
                      refine ⟨1691545456128894875437421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4510787883010386334499789 1691545456128894875437421)
                      ·
                        rfl

theorem cell23_3294273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_3294273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294273 prefixEnd_3294273 := by exact prefixLift 3294273
  have htrace : WordTrace (prefixWord ++ tailWord_3294273) baseStart_3294273 baseEnd_3294273 := by
    simpa [prefixWord, tailWord_3294273, baseEnd_3294273] using wordTrace_append hprefix tailTrace_3294273
  have hstable : (prefixWord ++ tailWord_3294273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294273).length < 2 ^ (prefixWord ++ tailWord_3294273).sum := by decide
  have hdescent : baseEnd_3294273 < baseStart_3294273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294285 : List Nat := [1, 6, 1, 1, 1, 2, 3, 8]
def baseStart_3294285 : Nat := 118140960795 + 3294285 * 2 ^ 59
def prefixEnd_3294285 : Nat := 4983230072969 + 3 ^ 40 * 3294285 * 2
def baseEnd_3294285 : Nat := 62650059922101808462495

theorem tailTrace_3294285 : CollatzResearch.WordTrace tailWord_3294285 prefixEnd_3294285 62650059922101808462495 := by
  unfold tailWord_3294285
  simp only [CollatzResearch.WordTrace]
  refine ⟨120152444870375538930716309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80101629913583692620477539 120152444870375538930716309)
  ·
    refine ⟨5632145853298853387377327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120152444870375538930716309 5632145853298853387377327)
    ·
      refine ⟨8448218779948280081065991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5632145853298853387377327 8448218779948280081065991)
      ·
        refine ⟨12672328169922420121598987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8448218779948280081065991 12672328169922420121598987)
        ·
          refine ⟨19008492254883630182398481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12672328169922420121598987 19008492254883630182398481)
          ·
            refine ⟨14256369191162722636798861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19008492254883630182398481 14256369191162722636798861)
            ·
              refine ⟨5346138446686020988799573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14256369191162722636798861 5346138446686020988799573)
              ·
                refine ⟨62650059922101808462495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5346138446686020988799573 62650059922101808462495)
                ·
                  rfl

theorem cell23_3294285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 8].length) (baseStart_3294285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294285 prefixEnd_3294285 := by exact prefixLift 3294285
  have htrace : WordTrace (prefixWord ++ tailWord_3294285) baseStart_3294285 baseEnd_3294285 := by
    simpa [prefixWord, tailWord_3294285, baseEnd_3294285] using wordTrace_append hprefix tailTrace_3294285
  have hstable : (prefixWord ++ tailWord_3294285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294285).length < 2 ^ (prefixWord ++ tailWord_3294285).sum := by decide
  have hdescent : baseEnd_3294285 < baseStart_3294285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294295 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 6, 1, 3]
def baseStart_3294295 : Nat := 118140960795 + 3294295 * 2 ^ 59
def prefixEnd_3294295 : Nat := 4983230072969 + 3 ^ 40 * 3294295 * 2
def baseEnd_3294295 : Nat := 1691556752703293789362319

theorem tailTrace_3294295 : CollatzResearch.WordTrace tailWord_3294295 prefixEnd_3294295 1691556752703293789362319 := by
  unfold tailWord_3294295
  simp only [CollatzResearch.WordTrace]
  refine ⟨120152809600339310638580339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80101873066892873759053559 120152809600339310638580339)
  ·
    refine ⟨180229214400508965957870509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120152809600339310638580339 180229214400508965957870509)
    ·
      refine ⟨67585955400190862234201441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180229214400508965957870509 67585955400190862234201441)
      ·
        refine ⟨50689466550143146675651081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67585955400190862234201441 50689466550143146675651081)
        ·
          refine ⟨38017099912607360006738311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50689466550143146675651081 38017099912607360006738311)
          ·
            refine ⟨57025649868911040010107467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38017099912607360006738311 57025649868911040010107467)
            ·
              refine ⟨85538474803366560015161201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57025649868911040010107467 85538474803366560015161201)
              ·
                refine ⟨64153856102524920011370901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85538474803366560015161201 64153856102524920011370901)
                ·
                  refine ⟨3007212004805855625533011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64153856102524920011370901 3007212004805855625533011)
                  ·
                    refine ⟨4510818007208783438299517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3007212004805855625533011 4510818007208783438299517)
                    ·
                      refine ⟨1691556752703293789362319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4510818007208783438299517 1691556752703293789362319)
                      ·
                        rfl

theorem cell23_3294295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_3294295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294295 prefixEnd_3294295 := by exact prefixLift 3294295
  have htrace : WordTrace (prefixWord ++ tailWord_3294295) baseStart_3294295 baseEnd_3294295 := by
    simpa [prefixWord, tailWord_3294295, baseEnd_3294295] using wordTrace_append hprefix tailTrace_3294295
  have hstable : (prefixWord ++ tailWord_3294295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294295).length < 2 ^ (prefixWord ++ tailWord_3294295).sum := by decide
  have hdescent : baseEnd_3294295 < baseStart_3294295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294308 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_3294308 : Nat := 118140960795 + 3294308 * 2 ^ 59
def prefixEnd_3294308 : Nat := 4983230072969 + 3 ^ 40 * 3294308 * 2
def baseEnd_3294308 : Nat := 1691563427951802238499759

theorem tailTrace_3294308 : CollatzResearch.WordTrace tailWord_3294308 prefixEnd_3294308 1691563427951802238499759 := by
  unfold tailWord_3294308
  simp only [CollatzResearch.WordTrace]
  refine ⟨60076641874646106929401789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80102189166194809239202385 60076641874646106929401789)
  ·
    refine ⟨22528740702992290098525671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60076641874646106929401789 22528740702992290098525671)
    ·
      refine ⟨33793111054488435147788507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22528740702992290098525671 33793111054488435147788507)
      ·
        refine ⟨50689666581732652721682761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33793111054488435147788507 50689666581732652721682761)
        ·
          refine ⟨38017249936299489541262071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50689666581732652721682761 38017249936299489541262071)
          ·
            refine ⟨57025874904449234311893107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38017249936299489541262071 57025874904449234311893107)
            ·
              refine ⟨85538812356673851467839661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57025874904449234311893107 85538812356673851467839661)
              ·
                refine ⟨32077054633752694300439873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85538812356673851467839661 32077054633752694300439873)
                ·
                  refine ⟨24057790975314520725329905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32077054633752694300439873 24057790975314520725329905)
                  ·
                    refine ⟨18043343231485890543997429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24057790975314520725329905 18043343231485890543997429)
                    ·
                      refine ⟨1691563427951802238499759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18043343231485890543997429 1691563427951802238499759)
                      ·
                        rfl

theorem cell23_3294308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_3294308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294308 prefixEnd_3294308 := by exact prefixLift 3294308
  have htrace : WordTrace (prefixWord ++ tailWord_3294308) baseStart_3294308 baseEnd_3294308 := by
    simpa [prefixWord, tailWord_3294308, baseEnd_3294308] using wordTrace_append hprefix tailTrace_3294308
  have hstable : (prefixWord ++ tailWord_3294308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294308).length < 2 ^ (prefixWord ++ tailWord_3294308).sum := by decide
  have hdescent : baseEnd_3294308 < baseStart_3294308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294328 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 2, 6]
def baseStart_3294328 : Nat := 118140960795 + 3294328 * 2 ^ 59
def prefixEnd_3294328 : Nat := 4983230072969 + 3 ^ 40 * 3294328 * 2
def baseEnd_3294328 : Nat := 563857899188297386749889

theorem tailTrace_3294328 : CollatzResearch.WordTrace tailWord_3294328 prefixEnd_3294328 563857899188297386749889 := by
  unfold tailWord_3294328
  simp only [CollatzResearch.WordTrace]
  refine ⟨60077006604609878637265819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80102675472813171516354425 60077006604609878637265819)
  ·
    refine ⟨90115509906914817955898729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60077006604609878637265819 90115509906914817955898729)
    ·
      refine ⟨67586632430186113466924047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90115509906914817955898729 67586632430186113466924047)
      ·
        refine ⟨101379948645279170200386071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67586632430186113466924047 101379948645279170200386071)
        ·
          refine ⟨152069922967918755300579107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101379948645279170200386071 152069922967918755300579107)
          ·
            refine ⟨228104884451878132950868661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152069922967918755300579107 228104884451878132950868661)
            ·
              refine ⟨21384832917363574964143937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 228104884451878132950868661 21384832917363574964143937)
              ·
                refine ⟨16038624688022681223107953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21384832917363574964143937 16038624688022681223107953)
                ·
                  refine ⟨12028968516017010917330965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16038624688022681223107953 12028968516017010917330965)
                  ·
                    refine ⟨563857899188297386749889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12028968516017010917330965 563857899188297386749889)
                    ·
                      rfl

theorem cell23_3294328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_3294328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294328 prefixEnd_3294328 := by exact prefixLift 3294328
  have htrace : WordTrace (prefixWord ++ tailWord_3294328) baseStart_3294328 baseEnd_3294328 := by
    simpa [prefixWord, tailWord_3294328, baseEnd_3294328] using wordTrace_append hprefix tailTrace_3294328
  have hstable : (prefixWord ++ tailWord_3294328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294328).length < 2 ^ (prefixWord ++ tailWord_3294328).sum := by decide
  have hdescent : baseEnd_3294328 < baseStart_3294328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294442 : List Nat := [3, 1, 3, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_3294442 : Nat := 118140960795 + 3294442 * 2 ^ 59
def prefixEnd_3294442 : Nat := 4983230072969 + 3 ^ 40 * 3294442 * 2
def baseEnd_3294442 : Nat := 1691632234359504714224143

theorem tailTrace_3294442 : CollatzResearch.WordTrace tailWord_3294442 prefixEnd_3294442 1691632234359504714224143 := by
  unfold tailWord_3294442
  simp only [CollatzResearch.WordTrace]
  refine ⟨30039542782701688686045395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80105447420537836496121053 30039542782701688686045395)
  ·
    refine ⟨45059314174052533029068093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30039542782701688686045395 45059314174052533029068093)
    ·
      refine ⟨16897242815269699885900535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45059314174052533029068093 16897242815269699885900535)
      ·
        refine ⟨25345864222904549828850803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16897242815269699885900535 25345864222904549828850803)
        ·
          refine ⟨38018796334356824743276205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25345864222904549828850803 38018796334356824743276205)
          ·
            refine ⟨14257048625383809278728577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38018796334356824743276205 14257048625383809278728577)
            ·
              refine ⟨10692786469037856959046433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14257048625383809278728577 10692786469037856959046433)
              ·
                refine ⟨8019589851778392719284825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10692786469037856959046433 8019589851778392719284825)
                ·
                  refine ⟨6014692388833794539463619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8019589851778392719284825 6014692388833794539463619)
                  ·
                    refine ⟨9022038583250691809195429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6014692388833794539463619 9022038583250691809195429)
                    ·
                      refine ⟨1691632234359504714224143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9022038583250691809195429 1691632234359504714224143)
                      ·
                        rfl

theorem cell23_3294442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_3294442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294442 prefixEnd_3294442 := by exact prefixLift 3294442
  have htrace : WordTrace (prefixWord ++ tailWord_3294442) baseStart_3294442 baseEnd_3294442 := by
    simpa [prefixWord, tailWord_3294442, baseEnd_3294442] using wordTrace_append hprefix tailTrace_3294442
  have hstable : (prefixWord ++ tailWord_3294442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294442).length < 2 ^ (prefixWord ++ tailWord_3294442).sum := by decide
  have hdescent : baseEnd_3294442 < baseStart_3294442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294529 : List Nat := [1, 2, 5, 2, 1, 1, 1, 4, 1, 5]
def baseStart_3294529 : Nat := 118140960795 + 3294529 * 2 ^ 59
def prefixEnd_3294529 : Nat := 4983230072969 + 3 ^ 40 * 3294529 * 2
def baseEnd_3294529 : Nat := 563892302392148624612081

theorem tailTrace_3294529 : CollatzResearch.WordTrace tailWord_3294529 prefixEnd_3294529 563892302392148624612081 := by
  unfold tailWord_3294529
  simp only [CollatzResearch.WordTrace]
  refine ⟨120161344281491568602598641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80107562854327712401732427 120161344281491568602598641)
  ·
    refine ⟨90121008211118676451948981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120161344281491568602598641 90121008211118676451948981)
    ·
      refine ⟨8448844519792375917370217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90121008211118676451948981 8448844519792375917370217)
      ·
        refine ⟨6336633389844281938027663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8448844519792375917370217 6336633389844281938027663)
        ·
          refine ⟨9504950084766422907041495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6336633389844281938027663 9504950084766422907041495)
          ·
            refine ⟨14257425127149634360562243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9504950084766422907041495 14257425127149634360562243)
            ·
              refine ⟨21386137690724451540843365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14257425127149634360562243 21386137690724451540843365)
              ·
                refine ⟨4009900817010834663908131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21386137690724451540843365 4009900817010834663908131)
                ·
                  refine ⟨6014851225516251995862197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4009900817010834663908131 6014851225516251995862197)
                  ·
                    refine ⟨563892302392148624612081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6014851225516251995862197 563892302392148624612081)
                    ·
                      rfl

theorem cell23_3294529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_3294529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294529 prefixEnd_3294529 := by exact prefixLift 3294529
  have htrace : WordTrace (prefixWord ++ tailWord_3294529) baseStart_3294529 baseEnd_3294529 := by
    simpa [prefixWord, tailWord_3294529, baseEnd_3294529] using wordTrace_append hprefix tailTrace_3294529
  have hstable : (prefixWord ++ tailWord_3294529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294529).length < 2 ^ (prefixWord ++ tailWord_3294529).sum := by decide
  have hdescent : baseEnd_3294529 < baseStart_3294529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294542 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 6, 4]
def baseStart_3294542 : Nat := 118140960795 + 3294542 * 2 ^ 59
def prefixEnd_3294542 : Nat := 4983230072969 + 3 ^ 40 * 3294542 * 2
def baseEnd_3294542 : Nat := 563894527474984774324561

theorem tailTrace_3294542 : CollatzResearch.WordTrace tailWord_3294542 prefixEnd_3294542 563894527474984774324561 := by
  unfold tailWord_3294542
  simp only [CollatzResearch.WordTrace]
  refine ⟨15020227303805558977852735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80107878953629647881881253 15020227303805558977852735)
  ·
    refine ⟨22530340955708338466779103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15020227303805558977852735 22530340955708338466779103)
    ·
      refine ⟨33795511433562507700168655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22530340955708338466779103 33795511433562507700168655)
      ·
        refine ⟨50693267150343761550252983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33795511433562507700168655 50693267150343761550252983)
        ·
          refine ⟨76039900725515642325379475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50693267150343761550252983 76039900725515642325379475)
          ·
            refine ⟨114059851088273463488069213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76039900725515642325379475 114059851088273463488069213)
            ·
              refine ⟨42772444158102548808025955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114059851088273463488069213 42772444158102548808025955)
              ·
                refine ⟨64158666237153823212038933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42772444158102548808025955 64158666237153823212038933)
                ·
                  refine ⟨3007437479866585463064325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64158666237153823212038933 3007437479866585463064325)
                  ·
                    refine ⟨563894527474984774324561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3007437479866585463064325 563894527474984774324561)
                    ·
                      rfl

theorem cell23_3294542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_3294542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294542 prefixEnd_3294542 := by exact prefixLift 3294542
  have htrace : WordTrace (prefixWord ++ tailWord_3294542) baseStart_3294542 baseEnd_3294542 := by
    simpa [prefixWord, tailWord_3294542, baseEnd_3294542] using wordTrace_append hprefix tailTrace_3294542
  have hstable : (prefixWord ++ tailWord_3294542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294542).length < 2 ^ (prefixWord ++ tailWord_3294542).sum := by decide
  have hdescent : baseEnd_3294542 < baseStart_3294542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294549 : List Nat := [1, 3, 2, 2, 3, 1, 2, 3, 1, 1, 4]
def baseStart_3294549 : Nat := 118140960795 + 3294549 * 2 ^ 59
def prefixEnd_3294549 : Nat := 4983230072969 + 3 ^ 40 * 3294549 * 2
def baseEnd_3294549 : Nat := 1691687176789535795586151

theorem tailTrace_3294549 : CollatzResearch.WordTrace tailWord_3294549 prefixEnd_3294549 1691687176789535795586151 := by
  unfold tailWord_3294549
  simp only [CollatzResearch.WordTrace]
  refine ⟨120162073741419112018326701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80108049160946074678884467 120162073741419112018326701)
  ·
    refine ⟨45060777653032167006872513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120162073741419112018326701 45060777653032167006872513)
    ·
      refine ⟨33795583239774125255154385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45060777653032167006872513 33795583239774125255154385)
      ·
        refine ⟨25346687429830593941365789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33795583239774125255154385 25346687429830593941365789)
        ·
          refine ⟨9505007786186472728012171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25346687429830593941365789 9505007786186472728012171)
          ·
            refine ⟨14257511679279709092018257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9505007786186472728012171 14257511679279709092018257)
            ·
              refine ⟨10693133759459781819013693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14257511679279709092018257 10693133759459781819013693)
              ·
                refine ⟨4009925159797418182130135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10693133759459781819013693 4009925159797418182130135)
                ·
                  refine ⟨6014887739696127273195203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4009925159797418182130135 6014887739696127273195203)
                  ·
                    refine ⟨9022331609544190909792805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6014887739696127273195203 9022331609544190909792805)
                    ·
                      refine ⟨1691687176789535795586151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9022331609544190909792805 1691687176789535795586151)
                      ·
                        rfl

theorem cell23_3294549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_3294549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294549 prefixEnd_3294549 := by exact prefixLift 3294549
  have htrace : WordTrace (prefixWord ++ tailWord_3294549) baseStart_3294549 baseEnd_3294549 := by
    simpa [prefixWord, tailWord_3294549, baseEnd_3294549] using wordTrace_append hprefix tailTrace_3294549
  have hstable : (prefixWord ++ tailWord_3294549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294549).length < 2 ^ (prefixWord ++ tailWord_3294549).sum := by decide
  have hdescent : baseEnd_3294549 < baseStart_3294549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294552 : List Nat := [2, 1, 2, 2, 1, 1, 6, 1, 1, 1, 5]
def baseStart_3294552 : Nat := 118140960795 + 3294552 * 2 ^ 59
def prefixEnd_3294552 : Nat := 4983230072969 + 3 ^ 40 * 3294552 * 2
def baseEnd_3294552 : Nat := 1691688717231499283848637

theorem tailTrace_3294552 : CollatzResearch.WordTrace tailWord_3294552 prefixEnd_3294552 1691688717231499283848637 := by
  unfold tailWord_3294552
  simp only [CollatzResearch.WordTrace]
  refine ⟨60081091580204121765342955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80108122106938829020457273 60081091580204121765342955)
  ·
    refine ⟨90121637370306182648014433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60081091580204121765342955 90121637370306182648014433)
    ·
      refine ⟨67591228027729636986010825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90121637370306182648014433 67591228027729636986010825)
      ·
        refine ⟨50693421020797227739508119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67591228027729636986010825 50693421020797227739508119)
        ·
          refine ⟨76040131531195841609262179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50693421020797227739508119 76040131531195841609262179)
          ·
            refine ⟨114060197296793762413893269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76040131531195841609262179 114060197296793762413893269)
            ·
              refine ⟨5346571748287207613151247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114060197296793762413893269 5346571748287207613151247)
              ·
                refine ⟨8019857622430811419726871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5346571748287207613151247 8019857622430811419726871)
                ·
                  refine ⟨12029786433646217129590307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8019857622430811419726871 12029786433646217129590307)
                  ·
                    refine ⟨18044679650469325694385461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12029786433646217129590307 18044679650469325694385461)
                    ·
                      refine ⟨1691688717231499283848637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18044679650469325694385461 1691688717231499283848637)
                      ·
                        rfl

theorem cell23_3294552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_3294552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294552 prefixEnd_3294552 := by exact prefixLift 3294552
  have htrace : WordTrace (prefixWord ++ tailWord_3294552) baseStart_3294552 baseEnd_3294552 := by
    simpa [prefixWord, tailWord_3294552, baseEnd_3294552] using wordTrace_append hprefix tailTrace_3294552
  have hstable : (prefixWord ++ tailWord_3294552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294552).length < 2 ^ (prefixWord ++ tailWord_3294552).sum := by decide
  have hdescent : baseEnd_3294552 < baseStart_3294552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294562 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_3294562 : Nat := 118140960795 + 3294562 * 2 ^ 59
def prefixEnd_3294562 : Nat := 4983230072969 + 3 ^ 40 * 3294562 * 2
def baseEnd_3294562 : Nat := 1691693852038044244723591

theorem tailTrace_3294562 : CollatzResearch.WordTrace tailWord_3294562 prefixEnd_3294562 1691693852038044244723591 := by
  unfold tailWord_3294562
  simp only [CollatzResearch.WordTrace]
  refine ⟨30040636972593003809637485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80108365260248010159033293 30040636972593003809637485)
  ·
    refine ⟨11265238864722376428614057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30040636972593003809637485 11265238864722376428614057)
    ·
      refine ⟨8448929148541782321460543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11265238864722376428614057 8448929148541782321460543)
      ·
        refine ⟨12673393722812673482190815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8448929148541782321460543 12673393722812673482190815)
        ·
          refine ⟨19010090584219010223286223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12673393722812673482190815 19010090584219010223286223)
          ·
            refine ⟨28515135876328515334929335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19010090584219010223286223 28515135876328515334929335)
            ·
              refine ⟨42772703814492773002394003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28515135876328515334929335 42772703814492773002394003)
              ·
                refine ⟨64159055721739159503591005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42772703814492773002394003 64159055721739159503591005)
                ·
                  refine ⟨24059645895652184813846627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64159055721739159503591005 24059645895652184813846627)
                  ·
                    refine ⟨36089468843478277220769941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24059645895652184813846627 36089468843478277220769941)
                    ·
                      refine ⟨1691693852038044244723591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36089468843478277220769941 1691693852038044244723591)
                      ·
                        rfl

theorem cell23_3294562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_3294562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294562 prefixEnd_3294562 := by exact prefixLift 3294562
  have htrace : WordTrace (prefixWord ++ tailWord_3294562) baseStart_3294562 baseEnd_3294562 := by
    simpa [prefixWord, tailWord_3294562, baseEnd_3294562] using wordTrace_append hprefix tailTrace_3294562
  have hstable : (prefixWord ++ tailWord_3294562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294562).length < 2 ^ (prefixWord ++ tailWord_3294562).sum := by decide
  have hdescent : baseEnd_3294562 < baseStart_3294562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294572 : List Nat := [2, 2, 1, 1, 5, 2, 2, 8]
def baseStart_3294572 : Nat := 118140960795 + 3294572 * 2 ^ 59
def prefixEnd_3294572 : Nat := 4983230072969 + 3 ^ 40 * 3294572 * 2
def baseEnd_3294572 : Nat := 62655518031281081688835

theorem tailTrace_3294572 : CollatzResearch.WordTrace tailWord_3294572 prefixEnd_3294572 62655518031281081688835 := by
  unfold tailWord_3294572
  simp only [CollatzResearch.WordTrace]
  refine ⟨60081456310167893473206985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80108608413557191297609313 60081456310167893473206985)
  ·
    refine ⟨45061092232625920104905239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60081456310167893473206985 45061092232625920104905239)
    ·
      refine ⟨67591638348938880157357859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45061092232625920104905239 67591638348938880157357859)
      ·
        refine ⟨101387457523408320236036789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67591638348938880157357859 101387457523408320236036789)
        ·
          refine ⟨9505074142819530022128449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101387457523408320236036789 9505074142819530022128449)
          ·
            refine ⟨7128805607114647516596337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9505074142819530022128449 7128805607114647516596337)
            ·
              refine ⟨5346604205335985637447253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7128805607114647516596337 5346604205335985637447253)
              ·
                refine ⟨62655518031281081688835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5346604205335985637447253 62655518031281081688835)
                ·
                  rfl

theorem cell23_3294572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 8].length) (baseStart_3294572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294572 prefixEnd_3294572 := by exact prefixLift 3294572
  have htrace : WordTrace (prefixWord ++ tailWord_3294572) baseStart_3294572 baseEnd_3294572 := by
    simpa [prefixWord, tailWord_3294572, baseEnd_3294572] using wordTrace_append hprefix tailTrace_3294572
  have hstable : (prefixWord ++ tailWord_3294572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294572).length < 2 ^ (prefixWord ++ tailWord_3294572).sum := by decide
  have hdescent : baseEnd_3294572 < baseStart_3294572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294575 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 6]
def baseStart_3294575 : Nat := 118140960795 + 3294575 * 2 ^ 59
def prefixEnd_3294575 : Nat := 4983230072969 + 3 ^ 40 * 3294575 * 2
def baseEnd_3294575 : Nat := 1691700527286552693861031

theorem tailTrace_3294575 : CollatzResearch.WordTrace tailWord_3294575 prefixEnd_3294575 1691700527286552693861031 := by
  unfold tailWord_3294575
  simp only [CollatzResearch.WordTrace]
  refine ⟨120163022039324918458773179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80108681359549945639182119 120163022039324918458773179)
  ·
    refine ⟨180244533058987377688159769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120163022039324918458773179 180244533058987377688159769)
    ·
      refine ⟨135183399794240533266119827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180244533058987377688159769 135183399794240533266119827)
      ·
        refine ⟨202775099691360799899179741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135183399794240533266119827 202775099691360799899179741)
        ·
          refine ⟨76040662384260299962192403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202775099691360799899179741 76040662384260299962192403)
          ·
            refine ⟨114060993576390449943288605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76040662384260299962192403 114060993576390449943288605)
            ·
              refine ⟨42772872591146418728733227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114060993576390449943288605 42772872591146418728733227)
              ·
                refine ⟨64159308886719628093099841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42772872591146418728733227 64159308886719628093099841)
                ·
                  refine ⟨48119481665039721069824881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64159308886719628093099841 48119481665039721069824881)
                  ·
                    refine ⟨36089611248779790802368661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48119481665039721069824881 36089611248779790802368661)
                    ·
                      refine ⟨1691700527286552693861031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36089611248779790802368661 1691700527286552693861031)
                      ·
                        rfl

theorem cell23_3294575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_3294575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294575 prefixEnd_3294575 := by exact prefixLift 3294575
  have htrace : WordTrace (prefixWord ++ tailWord_3294575) baseStart_3294575 baseEnd_3294575 := by
    simpa [prefixWord, tailWord_3294575, baseEnd_3294575] using wordTrace_append hprefix tailTrace_3294575
  have hstable : (prefixWord ++ tailWord_3294575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294575).length < 2 ^ (prefixWord ++ tailWord_3294575).sum := by decide
  have hdescent : baseEnd_3294575 < baseStart_3294575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294599 : List Nat := [1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 3]
def baseStart_3294599 : Nat := 118140960795 + 3294599 * 2 ^ 59
def prefixEnd_3294599 : Nat := 4983230072969 + 3 ^ 40 * 3294599 * 2
def baseEnd_3294599 : Nat := 1691712850822260599960921

theorem tailTrace_3294599 : CollatzResearch.WordTrace tailWord_3294599 prefixEnd_3294599 1691712850822260599960921 := by
  unfold tailWord_3294599
  simp only [CollatzResearch.WordTrace]
  refine ⟨120163897391237970557646851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80109264927491980371764567 120163897391237970557646851)
  ·
    refine ⟨180245846086856955836470277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120163897391237970557646851 180245846086856955836470277)
    ·
      refine ⟨33796096141285679219338177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180245846086856955836470277 33796096141285679219338177)
      ·
        refine ⟨25347072105964259414503633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33796096141285679219338177 25347072105964259414503633)
        ·
          refine ⟨19010304079473194560877725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25347072105964259414503633 19010304079473194560877725)
          ·
            refine ⟨7128864029802447960329147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19010304079473194560877725 7128864029802447960329147)
            ·
              refine ⟨10693296044703671940493721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7128864029802447960329147 10693296044703671940493721)
              ·
                refine ⟨8019972033527753955370291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10693296044703671940493721 8019972033527753955370291)
                ·
                  refine ⟨12029958050291630933055437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8019972033527753955370291 12029958050291630933055437)
                  ·
                    refine ⟨4511234268859361599895789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12029958050291630933055437 4511234268859361599895789)
                    ·
                      refine ⟨1691712850822260599960921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4511234268859361599895789 1691712850822260599960921)
                      ·
                        rfl

theorem cell23_3294599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_3294599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294599 prefixEnd_3294599 := by exact prefixLift 3294599
  have htrace : WordTrace (prefixWord ++ tailWord_3294599) baseStart_3294599 baseEnd_3294599 := by
    simpa [prefixWord, tailWord_3294599, baseEnd_3294599] using wordTrace_append hprefix tailTrace_3294599
  have hstable : (prefixWord ++ tailWord_3294599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294599).length < 2 ^ (prefixWord ++ tailWord_3294599).sum := by decide
  have hdescent : baseEnd_3294599 < baseStart_3294599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294626 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 3, 3, 2]
def baseStart_3294626 : Nat := 118140960795 + 3294626 * 2 ^ 59
def prefixEnd_3294626 : Nat := 4983230072969 + 3 ^ 40 * 3294626 * 2
def baseEnd_3294626 : Nat := 1691726714799931994323297

theorem tailTrace_3294626 : CollatzResearch.WordTrace tailWord_3294626 prefixEnd_3294626 1691726714799931994323297 := by
  unfold tailWord_3294626
  simp only [CollatzResearch.WordTrace]
  refine ⟨30041220540535038542219933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80109921441426769445919821 30041220540535038542219933)
  ·
    refine ⟨11265457702700639453332475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30041220540535038542219933 11265457702700639453332475)
    ·
      refine ⟨16898186554050959179998713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11265457702700639453332475 16898186554050959179998713)
      ·
        refine ⟨12673639915538219384999035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16898186554050959179998713 12673639915538219384999035)
        ·
          refine ⟨19010459873307329077498553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12673639915538219384999035 19010459873307329077498553)
          ·
            refine ⟨14257844904980496808123915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19010459873307329077498553 14257844904980496808123915)
            ·
              refine ⟨21386767357470745212185873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14257844904980496808123915 21386767357470745212185873)
              ·
                refine ⟨16040075518103058909139405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21386767357470745212185873 16040075518103058909139405)
                ·
                  refine ⟨6015028319288647090927277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16040075518103058909139405 6015028319288647090927277)
                  ·
                    refine ⟨2255635619733242659097729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6015028319288647090927277 2255635619733242659097729)
                    ·
                      refine ⟨1691726714799931994323297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2255635619733242659097729 1691726714799931994323297)
                      ·
                        rfl

theorem cell23_3294626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_3294626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294626 prefixEnd_3294626 := by exact prefixLift 3294626
  have htrace : WordTrace (prefixWord ++ tailWord_3294626) baseStart_3294626 baseEnd_3294626 := by
    simpa [prefixWord, tailWord_3294626, baseEnd_3294626] using wordTrace_append hprefix tailTrace_3294626
  have hstable : (prefixWord ++ tailWord_3294626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294626).length < 2 ^ (prefixWord ++ tailWord_3294626).sum := by decide
  have hdescent : baseEnd_3294626 < baseStart_3294626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294642 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_3294642 : Nat := 118140960795 + 3294642 * 2 ^ 59
def prefixEnd_3294642 : Nat := 4983230072969 + 3 ^ 40 * 3294642 * 2
def baseEnd_3294642 : Nat := 1691734930490403931723223

theorem tailTrace_3294642 : CollatzResearch.WordTrace tailWord_3294642 prefixEnd_3294642 1691734930490403931723223 := by
  unfold tailWord_3294642
  simp only [CollatzResearch.WordTrace]
  refine ⟨30041366432520547225365545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80110310486721459267641453 30041366432520547225365545)
  ·
    refine ⟨22531024824390410419024159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30041366432520547225365545 22531024824390410419024159)
    ·
      refine ⟨33796537236585615628536239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22531024824390410419024159 33796537236585615628536239)
      ·
        refine ⟨50694805854878423442804359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33796537236585615628536239 50694805854878423442804359)
        ·
          refine ⟨76042208782317635164206539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50694805854878423442804359 76042208782317635164206539)
          ·
            refine ⟨114063313173476452746309809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76042208782317635164206539 114063313173476452746309809)
            ·
              refine ⟨85547484880107339559732357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114063313173476452746309809 85547484880107339559732357)
              ·
                refine ⟨16040153415020126167449817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85547484880107339559732357 16040153415020126167449817)
                ·
                  refine ⟨12030115061265094625587363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16040153415020126167449817 12030115061265094625587363)
                  ·
                    refine ⟨18045172591897641938381045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12030115061265094625587363 18045172591897641938381045)
                    ·
                      refine ⟨1691734930490403931723223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18045172591897641938381045 1691734930490403931723223)
                      ·
                        rfl

theorem cell23_3294642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_3294642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294642 prefixEnd_3294642 := by exact prefixLift 3294642
  have htrace : WordTrace (prefixWord ++ tailWord_3294642) baseStart_3294642 baseEnd_3294642 := by
    simpa [prefixWord, tailWord_3294642, baseEnd_3294642] using wordTrace_append hprefix tailTrace_3294642
  have hstable : (prefixWord ++ tailWord_3294642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294642).length < 2 ^ (prefixWord ++ tailWord_3294642).sum := by decide
  have hdescent : baseEnd_3294642 < baseStart_3294642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294660 : List Nat := [2, 3, 3, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_3294660 : Nat := 118140960795 + 3294660 * 2 ^ 59
def prefixEnd_3294660 : Nat := 4983230072969 + 3 ^ 40 * 3294660 * 2
def baseEnd_3294660 : Nat := 1691744173142184861298141

theorem tailTrace_3294660 : CollatzResearch.WordTrace tailWord_3294660 prefixEnd_3294660 1691744173142184861298141 := by
  unfold tailWord_3294660
  simp only [CollatzResearch.WordTrace]
  refine ⟨60083061122008488987808717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80110748162677985317078289 60083061122008488987808717)
  ·
    refine ⟨22531147920753183370428269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60083061122008488987808717 22531147920753183370428269)
    ·
      refine ⟨8449180470282443763910601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22531147920753183370428269 8449180470282443763910601)
      ·
        refine ⟨6336885352711832822932951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8449180470282443763910601 6336885352711832822932951)
        ·
          refine ⟨9505328029067749234399427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6336885352711832822932951 9505328029067749234399427)
          ·
            refine ⟨14257992043601623851599141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9505328029067749234399427 14257992043601623851599141)
            ·
              refine ⟨2673373508175304472174839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14257992043601623851599141 2673373508175304472174839)
              ·
                refine ⟨4010060262262956708262259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2673373508175304472174839 4010060262262956708262259)
                ·
                  refine ⟨6015090393394435062393389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4010060262262956708262259 6015090393394435062393389)
                  ·
                    refine ⟨2255658897522913148397521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6015090393394435062393389 2255658897522913148397521)
                    ·
                      refine ⟨1691744173142184861298141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2255658897522913148397521 1691744173142184861298141)
                      ·
                        rfl

theorem cell23_3294660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_3294660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294660 prefixEnd_3294660 := by exact prefixLift 3294660
  have htrace : WordTrace (prefixWord ++ tailWord_3294660) baseStart_3294660 baseEnd_3294660 := by
    simpa [prefixWord, tailWord_3294660, baseEnd_3294660] using wordTrace_append hprefix tailTrace_3294660
  have hstable : (prefixWord ++ tailWord_3294660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294660).length < 2 ^ (prefixWord ++ tailWord_3294660).sum := by decide
  have hdescent : baseEnd_3294660 < baseStart_3294660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294672 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 3]
def baseStart_3294672 : Nat := 118140960795 + 3294672 * 2 ^ 59
def prefixEnd_3294672 : Nat := 4983230072969 + 3 ^ 40 * 3294672 * 2
def baseEnd_3294672 : Nat := 1691750334910038814348085

theorem tailTrace_3294672 : CollatzResearch.WordTrace tailWord_3294672 prefixEnd_3294672 1691750334910038814348085 := by
  unfold tailWord_3294672
  simp only [CollatzResearch.WordTrace]
  refine ⟨60083279959986752012527135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80111039946649002683369513 60083279959986752012527135)
  ·
    refine ⟨90124919939980128018790703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60083279959986752012527135 90124919939980128018790703)
    ·
      refine ⟨135187379909970192028186055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90124919939980128018790703 135187379909970192028186055)
      ·
        refine ⟨202781069864955288042279083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135187379909970192028186055 202781069864955288042279083)
        ·
          refine ⟨304171604797432932063418625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202781069864955288042279083 304171604797432932063418625)
          ·
            refine ⟨228128703598074699047563969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304171604797432932063418625 228128703598074699047563969)
            ·
              refine ⟨171096527698556024285672977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228128703598074699047563969 171096527698556024285672977)
              ·
                refine ⟨128322395773917018214254733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171096527698556024285672977 128322395773917018214254733)
                ·
                  refine ⟨48120898415218881830345525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128322395773917018214254733 48120898415218881830345525)
                  ·
                    refine ⟨4511334226426770171594893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48120898415218881830345525 4511334226426770171594893)
                    ·
                      refine ⟨1691750334910038814348085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4511334226426770171594893 1691750334910038814348085)
                      ·
                        rfl

theorem cell23_3294672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 3].length) (baseStart_3294672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294672 prefixEnd_3294672 := by exact prefixLift 3294672
  have htrace : WordTrace (prefixWord ++ tailWord_3294672) baseStart_3294672 baseEnd_3294672 := by
    simpa [prefixWord, tailWord_3294672, baseEnd_3294672] using wordTrace_append hprefix tailTrace_3294672
  have hstable : (prefixWord ++ tailWord_3294672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294672).length < 2 ^ (prefixWord ++ tailWord_3294672).sum := by decide
  have hdescent : baseEnd_3294672 < baseStart_3294672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294689 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 2, 3, 3]
def baseStart_3294689 : Nat := 118140960795 + 3294689 * 2 ^ 59
def prefixEnd_3294689 : Nat := 4983230072969 + 3 ^ 40 * 3294689 * 2
def baseEnd_3294689 : Nat := 1691759064081165247835507

theorem tailTrace_3294689 : CollatzResearch.WordTrace tailWord_3294689 prefixEnd_3294689 1691759064081165247835507 := by
  unfold tailWord_3294689
  simp only [CollatzResearch.WordTrace]
  refine ⟨120167179960911915928423121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80111453307274610618948747 120167179960911915928423121)
  ·
    refine ⟨90125384970683936946317341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120167179960911915928423121 90125384970683936946317341)
    ·
      refine ⟨33797019364006476354869003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90125384970683936946317341 33797019364006476354869003)
      ·
        refine ⟨50695529046009714532303505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33797019364006476354869003 50695529046009714532303505)
        ·
          refine ⟨38021646784507285899227629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50695529046009714532303505 38021646784507285899227629)
          ·
            refine ⟨14258117544190232212210361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38021646784507285899227629 14258117544190232212210361)
            ·
              refine ⟨10693588158142674159157771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14258117544190232212210361 10693588158142674159157771)
              ·
                refine ⟨16040382237214011238736657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10693588158142674159157771 16040382237214011238736657)
                ·
                  refine ⟨12030286677910508429052493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16040382237214011238736657 12030286677910508429052493)
                  ·
                    refine ⟨4511357504216440660894685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12030286677910508429052493 4511357504216440660894685)
                    ·
                      refine ⟨1691759064081165247835507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4511357504216440660894685 1691759064081165247835507)
                      ·
                        rfl

theorem cell23_3294689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_3294689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294689 prefixEnd_3294689 := by exact prefixLift 3294689
  have htrace : WordTrace (prefixWord ++ tailWord_3294689) baseStart_3294689 baseEnd_3294689 := by
    simpa [prefixWord, tailWord_3294689, baseEnd_3294689] using wordTrace_append hprefix tailTrace_3294689
  have hstable : (prefixWord ++ tailWord_3294689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294689).length < 2 ^ (prefixWord ++ tailWord_3294689).sum := by decide
  have hdescent : baseEnd_3294689 < baseStart_3294689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294729 : List Nat := [1, 2, 1, 1, 3, 1, 5, 2, 2, 1, 4]
def baseStart_3294729 : Nat := 118140960795 + 3294729 * 2 ^ 59
def prefixEnd_3294729 : Nat := 4983230072969 + 3 ^ 40 * 3294729 * 2
def baseEnd_3294729 : Nat := 1691779603307345091335323

theorem tailTrace_3294729 : CollatzResearch.WordTrace tailWord_3294729 prefixEnd_3294729 1691779603307345091335323 := by
  unfold tailWord_3294729
  simp only [CollatzResearch.WordTrace]
  refine ⟨120168638880767002759879241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80112425920511335173252827 120168638880767002759879241)
  ·
    refine ⟨90126479160575252069909431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120168638880767002759879241 90126479160575252069909431)
    ·
      refine ⟨135189718740862878104864147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90126479160575252069909431 135189718740862878104864147)
      ·
        refine ⟨202784578111294317157296221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135189718740862878104864147 202784578111294317157296221)
        ·
          refine ⟨76044216791735368933986083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202784578111294317157296221 76044216791735368933986083)
          ·
            refine ⟨114066325187603053400979125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76044216791735368933986083 114066325187603053400979125)
            ·
              refine ⟨10693717986337786256341793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114066325187603053400979125 10693717986337786256341793)
              ·
                refine ⟨8020288489753339692256345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10693717986337786256341793 8020288489753339692256345)
                ·
                  refine ⟨6015216367315004769192259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8020288489753339692256345 6015216367315004769192259)
                  ·
                    refine ⟨9022824550972507153788389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6015216367315004769192259 9022824550972507153788389)
                    ·
                      refine ⟨1691779603307345091335323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9022824550972507153788389 1691779603307345091335323)
                      ·
                        rfl

theorem cell23_3294729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 1, 4].length) (baseStart_3294729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294729 prefixEnd_3294729 := by exact prefixLift 3294729
  have htrace : WordTrace (prefixWord ++ tailWord_3294729) baseStart_3294729 baseEnd_3294729 := by
    simpa [prefixWord, tailWord_3294729, baseEnd_3294729] using wordTrace_append hprefix tailTrace_3294729
  have hstable : (prefixWord ++ tailWord_3294729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294729).length < 2 ^ (prefixWord ++ tailWord_3294729).sum := by decide
  have hdescent : baseEnd_3294729 < baseStart_3294729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294823 : List Nat := [1, 1, 5, 1, 1, 1, 5, 1, 2, 3, 2]
def baseStart_3294823 : Nat := 118140960795 + 3294823 * 2 ^ 59
def prefixEnd_3294823 : Nat := 4983230072969 + 3 ^ 40 * 3294823 * 2
def baseEnd_3294823 : Nat := 1691827870488867723559891

theorem tailTrace_3294823 : CollatzResearch.WordTrace tailWord_3294823 prefixEnd_3294823 1691827870488867723559891 := by
  unfold tailWord_3294823
  simp only [CollatzResearch.WordTrace]
  refine ⟨120172067342426456813801123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80114711561617637875867415 120172067342426456813801123)
  ·
    refine ⟨180258101013639685220701685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120172067342426456813801123 180258101013639685220701685)
    ·
      refine ⟨16899196970028720489440783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180258101013639685220701685 16899196970028720489440783)
      ·
        refine ⟨25348795455043080734161175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16899196970028720489440783 25348795455043080734161175)
        ·
          refine ⟨38023193182564621101241763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25348795455043080734161175 38023193182564621101241763)
          ·
            refine ⟨57034789773846931651862645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38023193182564621101241763 57034789773846931651862645)
            ·
              refine ⟨5347011541298149842362123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57034789773846931651862645 5347011541298149842362123)
              ·
                refine ⟨8020517311947224763543185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5347011541298149842362123 8020517311947224763543185)
                ·
                  refine ⟨6015387983960418572657389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8020517311947224763543185 6015387983960418572657389)
                  ·
                    refine ⟨2255770493985156964746521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6015387983960418572657389 2255770493985156964746521)
                    ·
                      refine ⟨1691827870488867723559891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2255770493985156964746521 1691827870488867723559891)
                      ·
                        rfl

theorem cell23_3294823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_3294823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294823 prefixEnd_3294823 := by exact prefixLift 3294823
  have htrace : WordTrace (prefixWord ++ tailWord_3294823) baseStart_3294823 baseEnd_3294823 := by
    simpa [prefixWord, tailWord_3294823, baseEnd_3294823] using wordTrace_append hprefix tailTrace_3294823
  have hstable : (prefixWord ++ tailWord_3294823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294823).length < 2 ^ (prefixWord ++ tailWord_3294823).sum := by decide
  have hdescent : baseEnd_3294823 < baseStart_3294823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294839 : List Nat := [1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 5]
def baseStart_3294839 : Nat := 118140960795 + 3294839 * 2 ^ 59
def prefixEnd_3294839 : Nat := 4983230072969 + 3 ^ 40 * 3294839 * 2
def baseEnd_3294839 : Nat := 1691836086179339660959817

theorem tailTrace_3294839 : CollatzResearch.WordTrace tailWord_3294839 prefixEnd_3294839 1691836086179339660959817 := by
  unfold tailWord_3294839
  simp only [CollatzResearch.WordTrace]
  refine ⟨120172650910368491546383571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80115100606912327697589047 120172650910368491546383571)
  ·
    refine ⟨180258976365552737319575357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120172650910368491546383571 180258976365552737319575357)
    ·
      refine ⟨67597116137082276494840759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180258976365552737319575357 67597116137082276494840759)
      ·
        refine ⟨101395674205623414742261139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67597116137082276494840759 101395674205623414742261139)
        ·
          refine ⟨152093511308435122113391709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101395674205623414742261139 152093511308435122113391709)
          ·
            refine ⟨57035066740663170792521891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152093511308435122113391709 57035066740663170792521891)
            ·
              refine ⟨85552600110994756188782837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57035066740663170792521891 85552600110994756188782837)
              ·
                refine ⟨8020556260405758392698391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85552600110994756188782837 8020556260405758392698391)
                ·
                  refine ⟨12030834390608637589047587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8020556260405758392698391 12030834390608637589047587)
                  ·
                    refine ⟨18046251585912956383571381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12030834390608637589047587 18046251585912956383571381)
                    ·
                      refine ⟨1691836086179339660959817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18046251585912956383571381 1691836086179339660959817)
                      ·
                        rfl

theorem cell23_3294839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_3294839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294839 prefixEnd_3294839 := by exact prefixLift 3294839
  have htrace : WordTrace (prefixWord ++ tailWord_3294839) baseStart_3294839 baseEnd_3294839 := by
    simpa [prefixWord, tailWord_3294839, baseEnd_3294839] using wordTrace_append hprefix tailTrace_3294839
  have hstable : (prefixWord ++ tailWord_3294839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294839).length < 2 ^ (prefixWord ++ tailWord_3294839).sum := by decide
  have hdescent : baseEnd_3294839 < baseStart_3294839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294876 : List Nat := [2, 2, 3, 2, 3, 1, 1, 9]
def baseStart_3294876 : Nat := 118140960795 + 3294876 * 2 ^ 59
def prefixEnd_3294876 : Nat := 4983230072969 + 3 ^ 40 * 3294876 * 2
def baseEnd_3294876 : Nat := 62661299443094667266561

theorem tailTrace_3294876 : CollatzResearch.WordTrace tailWord_3294876 prefixEnd_3294876 62661299443094667266561 := by
  unfold tailWord_3294876
  simp only [CollatzResearch.WordTrace]
  refine ⟨60087000205617223432740241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80116000274156297910320321 60087000205617223432740241)
  ·
    refine ⟨45065250154212917574555181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60087000205617223432740241 45065250154212917574555181)
    ·
      refine ⟨16899468807829844090458193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45065250154212917574555181 16899468807829844090458193)
      ·
        refine ⟨12674601605872383067843645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16899468807829844090458193 12674601605872383067843645)
        ·
          refine ⟨4752975602202143650441367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12674601605872383067843645 4752975602202143650441367)
          ·
            refine ⟨7129463403303215475662051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4752975602202143650441367 7129463403303215475662051)
            ·
              refine ⟨10694195104954823213493077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7129463403303215475662051 10694195104954823213493077)
              ·
                refine ⟨62661299443094667266561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10694195104954823213493077 62661299443094667266561)
                ·
                  rfl

theorem cell23_3294876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 9].length) (baseStart_3294876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294876 prefixEnd_3294876 := by exact prefixLift 3294876
  have htrace : WordTrace (prefixWord ++ tailWord_3294876) baseStart_3294876 baseEnd_3294876 := by
    simpa [prefixWord, tailWord_3294876, baseEnd_3294876] using wordTrace_append hprefix tailTrace_3294876
  have hstable : (prefixWord ++ tailWord_3294876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294876).length < 2 ^ (prefixWord ++ tailWord_3294876).sum := by decide
  have hdescent : baseEnd_3294876 < baseStart_3294876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294899 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 5]
def baseStart_3294899 : Nat := 118140960795 + 3294899 * 2 ^ 59
def prefixEnd_3294899 : Nat := 4983230072969 + 3 ^ 40 * 3294899 * 2
def baseEnd_3294899 : Nat := 1691866895018609426209541

theorem tailTrace_3294899 : CollatzResearch.WordTrace tailWord_3294899 prefixEnd_3294899 1691866895018609426209541 := by
  unfold tailWord_3294899
  simp only [CollatzResearch.WordTrace]
  refine ⟨120174839290151121793567751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80116559526767414529045167 120174839290151121793567751)
  ·
    refine ⟨180262258935226682690351627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120174839290151121793567751 180262258935226682690351627)
    ·
      refine ⟨270393388402840024035527441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180262258935226682690351627 270393388402840024035527441)
      ·
        refine ⟨202795041302130018026645581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270393388402840024035527441 202795041302130018026645581)
        ·
          refine ⟨76048140488298756759992093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202795041302130018026645581 76048140488298756759992093)
          ·
            refine ⟨28518052683112033784997035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76048140488298756759992093 28518052683112033784997035)
            ·
              refine ⟨42777079024668050677495553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28518052683112033784997035 42777079024668050677495553)
              ·
                refine ⟨32082809268501038008121665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42777079024668050677495553 32082809268501038008121665)
                ·
                  refine ⟨24062106951375778506091249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32082809268501038008121665 24062106951375778506091249)
                  ·
                    refine ⟨18046580213531833879568437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24062106951375778506091249 18046580213531833879568437)
                    ·
                      refine ⟨1691866895018609426209541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18046580213531833879568437 1691866895018609426209541)
                      ·
                        rfl

theorem cell23_3294899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_3294899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294899 prefixEnd_3294899 := by exact prefixLift 3294899
  have htrace : WordTrace (prefixWord ++ tailWord_3294899) baseStart_3294899 baseEnd_3294899 := by
    simpa [prefixWord, tailWord_3294899, baseEnd_3294899] using wordTrace_append hprefix tailTrace_3294899
  have hstable : (prefixWord ++ tailWord_3294899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294899).length < 2 ^ (prefixWord ++ tailWord_3294899).sum := by decide
  have hdescent : baseEnd_3294899 < baseStart_3294899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294903 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 4, 1, 3]
def baseStart_3294903 : Nat := 118140960795 + 3294903 * 2 ^ 59
def prefixEnd_3294903 : Nat := 4983230072969 + 3 ^ 40 * 3294903 * 2
def baseEnd_3294903 : Nat := 1691868948941227410559523

theorem tailTrace_3294903 : CollatzResearch.WordTrace tailWord_3294903 prefixEnd_3294903 1691868948941227410559523 := by
  unfold tailWord_3294903
  simp only [CollatzResearch.WordTrace]
  refine ⟨120174985182136630476713363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80116656788091086984475575 120174985182136630476713363)
  ·
    refine ⟨180262477773204945715070045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120174985182136630476713363 180262477773204945715070045)
    ·
      refine ⟨67598429164951854643151267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180262477773204945715070045 67598429164951854643151267)
      ·
        refine ⟨101397643747427781964726901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67598429164951854643151267 101397643747427781964726901)
        ·
          refine ⟨9506029101321354559193147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101397643747427781964726901 9506029101321354559193147)
          ·
            refine ⟨14259043651982031838789721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9506029101321354559193147 14259043651982031838789721)
            ·
              refine ⟨10694282738986523879092291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14259043651982031838789721 10694282738986523879092291)
              ·
                refine ⟨16041424108479785818638437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10694282738986523879092291 16041424108479785818638437)
                ·
                  refine ⟨3007767020339959840994707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16041424108479785818638437 3007767020339959840994707)
                  ·
                    refine ⟨4511650530509939761492061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3007767020339959840994707 4511650530509939761492061)
                    ·
                      refine ⟨1691868948941227410559523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4511650530509939761492061 1691868948941227410559523)
                      ·
                        rfl

theorem cell23_3294903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 1, 3].length) (baseStart_3294903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294903 prefixEnd_3294903 := by exact prefixLift 3294903
  have htrace : WordTrace (prefixWord ++ tailWord_3294903) baseStart_3294903 baseEnd_3294903 := by
    simpa [prefixWord, tailWord_3294903, baseEnd_3294903] using wordTrace_append hprefix tailTrace_3294903
  have hstable : (prefixWord ++ tailWord_3294903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294903).length < 2 ^ (prefixWord ++ tailWord_3294903).sum := by decide
  have hdescent : baseEnd_3294903 < baseStart_3294903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294914 : List Nat := [3, 5, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_3294914 : Nat := 118140960795 + 3294914 * 2 ^ 59
def prefixEnd_3294914 : Nat := 4983230072969 + 3 ^ 40 * 3294914 * 2
def baseEnd_3294914 : Nat := 563958199076142289173991

theorem tailTrace_3294914 : CollatzResearch.WordTrace tailWord_3294914 prefixEnd_3294914 563958199076142289173991 := by
  unfold tailWord_3294914
  simp only [CollatzResearch.WordTrace]
  refine ⟨30043846596274194838840949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80116924256731186236909197 30043846596274194838840949)
  ·
    refine ⟨2816610618400705766141339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30043846596274194838840949 2816610618400705766141339)
    ·
      refine ⟨4224915927601058649212009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2816610618400705766141339 4224915927601058649212009)
      ·
        refine ⟨3168686945700793986909007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4224915927601058649212009 3168686945700793986909007)
        ·
          refine ⟨4753030418551190980363511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3168686945700793986909007 4753030418551190980363511)
          ·
            refine ⟨7129545627826786470545267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4753030418551190980363511 7129545627826786470545267)
            ·
              refine ⟨10694318441740179705817901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7129545627826786470545267 10694318441740179705817901)
              ·
                refine ⟨4010369415652567389681713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10694318441740179705817901 4010369415652567389681713)
                ·
                  refine ⟨3007777061739425542261285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4010369415652567389681713 3007777061739425542261285)
                  ·
                    refine ⟨563958199076142289173991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3007777061739425542261285 563958199076142289173991)
                    ·
                      rfl

theorem cell23_3294914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_3294914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294914 prefixEnd_3294914 := by exact prefixLift 3294914
  have htrace : WordTrace (prefixWord ++ tailWord_3294914) baseStart_3294914 baseEnd_3294914 := by
    simpa [prefixWord, tailWord_3294914, baseEnd_3294914] using wordTrace_append hprefix tailTrace_3294914
  have hstable : (prefixWord ++ tailWord_3294914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294914).length < 2 ^ (prefixWord ++ tailWord_3294914).sum := by decide
  have hdescent : baseEnd_3294914 < baseStart_3294914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294919 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 1, 8]
def baseStart_3294919 : Nat := 118140960795 + 3294919 * 2 ^ 59
def prefixEnd_3294919 : Nat := 4983230072969 + 3 ^ 40 * 3294919 * 2
def baseEnd_3294919 : Nat := 563959054877233115986483

theorem tailTrace_3294919 : CollatzResearch.WordTrace tailWord_3294919 prefixEnd_3294919 563959054877233115986483 := by
  unfold tailWord_3294919
  simp only [CollatzResearch.WordTrace]
  refine ⟨120175568750078665209295811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80117045833385776806197207 120175568750078665209295811)
  ·
    refine ⟨180263353125117997813943717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120175568750078665209295811 180263353125117997813943717)
    ·
      refine ⟨33799378710959624590114447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180263353125117997813943717 33799378710959624590114447)
      ·
        refine ⟨50699068066439436885171671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33799378710959624590114447 50699068066439436885171671)
        ·
          refine ⟨76048602099659155327757507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50699068066439436885171671 76048602099659155327757507)
          ·
            refine ⟨114072903149488732991636261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76048602099659155327757507 114072903149488732991636261)
            ·
              refine ⟨21388669340529137435931799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114072903149488732991636261 21388669340529137435931799)
              ·
                refine ⟨32083004010793706153897699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21388669340529137435931799 32083004010793706153897699)
                ·
                  refine ⟨48124506016190559230846549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32083004010793706153897699 48124506016190559230846549)
                  ·
                    refine ⟨563959054877233115986483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48124506016190559230846549 563959054877233115986483)
                    ·
                      rfl

theorem cell23_3294919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_3294919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294919 prefixEnd_3294919 := by exact prefixLift 3294919
  have htrace : WordTrace (prefixWord ++ tailWord_3294919) baseStart_3294919 baseEnd_3294919 := by
    simpa [prefixWord, tailWord_3294919, baseEnd_3294919] using wordTrace_append hprefix tailTrace_3294919
  have hstable : (prefixWord ++ tailWord_3294919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294919).length < 2 ^ (prefixWord ++ tailWord_3294919).sum := by decide
  have hdescent : baseEnd_3294919 < baseStart_3294919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294930 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 3, 3, 2]
def baseStart_3294930 : Nat := 118140960795 + 3294930 * 2 ^ 59
def prefixEnd_3294930 : Nat := 4983230072969 + 3 ^ 40 * 3294930 * 2
def baseEnd_3294930 : Nat := 1691882812918898804921899

theorem tailTrace_3294930 : CollatzResearch.WordTrace tailWord_3294930 prefixEnd_3294930 1691882812918898804921899 := by
  unfold tailWord_3294930
  simp only [CollatzResearch.WordTrace]
  refine ⟨30043992488259703521986561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80117313302025876058630829 30043992488259703521986561)
  ·
    refine ⟨22532994366194777641489921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30043992488259703521986561 22532994366194777641489921)
    ·
      refine ⟨16899745774646083231117441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22532994366194777641489921 16899745774646083231117441)
      ·
        refine ⟨12674809330984562423338081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16899745774646083231117441 12674809330984562423338081)
        ·
          refine ⟨9506106998238421817503561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12674809330984562423338081 9506106998238421817503561)
          ·
            refine ⟨7129580248678816363127671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9506106998238421817503561 7129580248678816363127671)
            ·
              refine ⟨10694370373018224544691507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7129580248678816363127671 10694370373018224544691507)
              ·
                refine ⟨16041555559527336817037261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10694370373018224544691507 16041555559527336817037261)
                ·
                  refine ⟨6015583334822751306388973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16041555559527336817037261 6015583334822751306388973)
                  ·
                    refine ⟨2255843750558531739895865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6015583334822751306388973 2255843750558531739895865)
                    ·
                      refine ⟨1691882812918898804921899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2255843750558531739895865 1691882812918898804921899)
                      ·
                        rfl

theorem cell23_3294930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_3294930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294930 prefixEnd_3294930 := by exact prefixLift 3294930
  have htrace : WordTrace (prefixWord ++ tailWord_3294930) baseStart_3294930 baseEnd_3294930 := by
    simpa [prefixWord, tailWord_3294930, baseEnd_3294930] using wordTrace_append hprefix tailTrace_3294930
  have hstable : (prefixWord ++ tailWord_3294930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294930).length < 2 ^ (prefixWord ++ tailWord_3294930).sum := by decide
  have hdescent : baseEnd_3294930 < baseStart_3294930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294943 : List Nat := [1, 1, 2, 3, 2, 2, 3, 2, 1, 4, 2]
def baseStart_3294943 : Nat := 118140960795 + 3294943 * 2 ^ 59
def prefixEnd_3294943 : Nat := 4983230072969 + 3 ^ 40 * 3294943 * 2
def baseEnd_3294943 : Nat := 1691889488167407254059339

theorem tailTrace_3294943 : CollatzResearch.WordTrace tailWord_3294943 prefixEnd_3294943 1691889488167407254059339 := by
  unfold tailWord_3294943
  simp only [CollatzResearch.WordTrace]
  refine ⟨120176444101991717308169483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80117629401327811538779655 120176444101991717308169483)
  ·
    refine ⟨180264666152987575962254225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120176444101991717308169483 180264666152987575962254225)
    ·
      refine ⟨135198499614740681971690669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180264666152987575962254225 135198499614740681971690669)
      ·
        refine ⟨50699437355527755739384001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135198499614740681971690669 50699437355527755739384001)
        ·
          refine ⟨38024578016645816804538001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50699437355527755739384001 38024578016645816804538001)
          ·
            refine ⟨28518433512484362603403501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38024578016645816804538001 28518433512484362603403501)
            ·
              refine ⟨10694412567181635976276313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28518433512484362603403501 10694412567181635976276313)
              ·
                refine ⟨8020809425386226982207235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10694412567181635976276313 8020809425386226982207235)
                ·
                  refine ⟨12031214138079340473310853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8020809425386226982207235 12031214138079340473310853)
                  ·
                    refine ⟨2255852650889876338745785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12031214138079340473310853 2255852650889876338745785)
                    ·
                      refine ⟨1691889488167407254059339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2255852650889876338745785 1691889488167407254059339)
                      ·
                        rfl

theorem cell23_3294943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_3294943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294943 prefixEnd_3294943 := by exact prefixLift 3294943
  have htrace : WordTrace (prefixWord ++ tailWord_3294943) baseStart_3294943 baseEnd_3294943 := by
    simpa [prefixWord, tailWord_3294943, baseEnd_3294943] using wordTrace_append hprefix tailTrace_3294943
  have hstable : (prefixWord ++ tailWord_3294943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294943).length < 2 ^ (prefixWord ++ tailWord_3294943).sum := by decide
  have hdescent : baseEnd_3294943 < baseStart_3294943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294969 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 8]
def baseStart_3294969 : Nat := 118140960795 + 3294969 * 2 ^ 59
def prefixEnd_3294969 : Nat := 4983230072969 + 3 ^ 40 * 3294969 * 2
def baseEnd_3294969 : Nat := 1691902838664424152334219

theorem tailTrace_3294969 : CollatzResearch.WordTrace tailWord_3294969 prefixEnd_3294969 1691902838664424152334219 := by
  unfold tailWord_3294969
  simp only [CollatzResearch.WordTrace]
  refine ⟨120177392399897523748615961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80118261599931682499077307 120177392399897523748615961)
  ·
    refine ⟨90133044299923142811461971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120177392399897523748615961 90133044299923142811461971)
    ·
      refine ⟨135199566449884714217192957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90133044299923142811461971 135199566449884714217192957)
      ·
        refine ⟨50699837418706767831447359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135199566449884714217192957 50699837418706767831447359)
        ·
          refine ⟨76049756128060151747171039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50699837418706767831447359 76049756128060151747171039)
          ·
            refine ⟨114074634192090227620756559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76049756128060151747171039 114074634192090227620756559)
            ·
              refine ⟨171111951288135341431134839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114074634192090227620756559 171111951288135341431134839)
              ·
                refine ⟨256667926932203012146702259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171111951288135341431134839 256667926932203012146702259)
                ·
                  refine ⟨385001890398304518220053389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256667926932203012146702259 385001890398304518220053389)
                  ·
                    refine ⟨144375708899364194332520021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 385001890398304518220053389 144375708899364194332520021)
                    ·
                      refine ⟨1691902838664424152334219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 144375708899364194332520021 1691902838664424152334219)
                      ·
                        rfl

theorem cell23_3294969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_3294969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294969 prefixEnd_3294969 := by exact prefixLift 3294969
  have htrace : WordTrace (prefixWord ++ tailWord_3294969) baseStart_3294969 baseEnd_3294969 := by
    simpa [prefixWord, tailWord_3294969, baseEnd_3294969] using wordTrace_append hprefix tailTrace_3294969
  have hstable : (prefixWord ++ tailWord_3294969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294969).length < 2 ^ (prefixWord ++ tailWord_3294969).sum := by decide
  have hdescent : baseEnd_3294969 < baseStart_3294969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294976 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 3]
def baseStart_3294976 : Nat := 118140960795 + 3294976 * 2 ^ 59
def prefixEnd_3294976 : Nat := 4983230072969 + 3 ^ 40 * 3294976 * 2
def baseEnd_3294976 : Nat := 1691906433029005624946687

theorem tailTrace_3294976 : CollatzResearch.WordTrace tailWord_3294976 prefixEnd_3294976 1691906433029005624946687 := by
  unfold tailWord_3294976
  simp only [CollatzResearch.WordTrace]
  refine ⟨60088823855436081972060391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80118431807248109296080521 60088823855436081972060391)
  ·
    refine ⟨90133235783154122958090587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60088823855436081972060391 90133235783154122958090587)
    ·
      refine ⟨135199853674731184437135881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90133235783154122958090587 135199853674731184437135881)
      ·
        refine ⟨101399890256048388327851911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135199853674731184437135881 101399890256048388327851911)
        ·
          refine ⟨152099835384072582491777867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101399890256048388327851911 152099835384072582491777867)
          ·
            refine ⟨228149753076108873737666801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152099835384072582491777867 228149753076108873737666801)
            ·
              refine ⟨171112314807081655303250101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228149753076108873737666801 171112314807081655303250101)
              ·
                refine ⟨16041779513163905184679697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 171112314807081655303250101 16041779513163905184679697)
                ·
                  refine ⟨12031334634872928888509773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16041779513163905184679697 12031334634872928888509773)
                  ·
                    refine ⟨4511750488077348333191165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12031334634872928888509773 4511750488077348333191165)
                    ·
                      refine ⟨1691906433029005624946687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4511750488077348333191165 1691906433029005624946687)
                      ·
                        rfl

theorem cell23_3294976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_3294976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294976 prefixEnd_3294976 := by exact prefixLift 3294976
  have htrace : WordTrace (prefixWord ++ tailWord_3294976) baseStart_3294976 baseEnd_3294976 := by
    simpa [prefixWord, tailWord_3294976, baseEnd_3294976] using wordTrace_append hprefix tailTrace_3294976
  have hstable : (prefixWord ++ tailWord_3294976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294976).length < 2 ^ (prefixWord ++ tailWord_3294976).sum := by decide
  have hdescent : baseEnd_3294976 < baseStart_3294976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294983 : List Nat := [1, 1, 4, 4, 2, 1, 1, 2, 7]
def baseStart_3294983 : Nat := 118140960795 + 3294983 * 2 ^ 59
def prefixEnd_3294983 : Nat := 4983230072969 + 3 ^ 40 * 3294983 * 2
def baseEnd_3294983 : Nat := 187990003043731899728795

theorem tailTrace_3294983 : CollatzResearch.WordTrace tailWord_3294983 prefixEnd_3294983 187990003043731899728795 := by
  unfold tailWord_3294983
  simp only [CollatzResearch.WordTrace]
  refine ⟨120177903021846804139625603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80118602014564536093083735 120177903021846804139625603)
  ·
    refine ⟨180266854532770206209438405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120177903021846804139625603 180266854532770206209438405)
    ·
      refine ⟨33800035224894413664269701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180266854532770206209438405 33800035224894413664269701)
      ·
        refine ⟨6337506604667702562050569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33800035224894413664269701 6337506604667702562050569)
        ·
          refine ⟨4753129953500776921537927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6337506604667702562050569 4753129953500776921537927)
          ·
            refine ⟨7129694930251165382306891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4753129953500776921537927 7129694930251165382306891)
            ·
              refine ⟨10694542395376748073460337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7129694930251165382306891 10694542395376748073460337)
              ·
                refine ⟨8020906796532561055095253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10694542395376748073460337 8020906796532561055095253)
                ·
                  refine ⟨187990003043731899728795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8020906796532561055095253 187990003043731899728795)
                  ·
                    rfl

theorem cell23_3294983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 7].length) (baseStart_3294983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3294983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3294983 prefixEnd_3294983 := by exact prefixLift 3294983
  have htrace : WordTrace (prefixWord ++ tailWord_3294983) baseStart_3294983 baseEnd_3294983 := by
    simpa [prefixWord, tailWord_3294983, baseEnd_3294983] using wordTrace_append hprefix tailTrace_3294983
  have hstable : (prefixWord ++ tailWord_3294983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294983).length < 2 ^ (prefixWord ++ tailWord_3294983).sum := by decide
  have hdescent : baseEnd_3294983 < baseStart_3294983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295043 : List Nat := [1, 1, 1, 3, 1, 5, 2, 2, 3, 4]
def baseStart_3295043 : Nat := 118140960795 + 3295043 * 2 ^ 59
def prefixEnd_3295043 : Nat := 4983230072969 + 3 ^ 40 * 3295043 * 2
def baseEnd_3295043 : Nat := 563980278744285620936293

theorem tailTrace_3295043 : CollatzResearch.WordTrace tailWord_3295043 prefixEnd_3295043 563980278744285620936293 := by
  unfold tailWord_3295043
  simp only [CollatzResearch.WordTrace]
  refine ⟨120180091401629434386809783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80120060934419622924539855 120180091401629434386809783)
  ·
    refine ⟨180270137102444151580214675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120180091401629434386809783 180270137102444151580214675)
    ·
      refine ⟨270405205653666227370322013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180270137102444151580214675 270405205653666227370322013)
      ·
        refine ⟨101401952120124835263870755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270405205653666227370322013 101401952120124835263870755)
        ·
          refine ⟨152102928180187252895806133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101401952120124835263870755 152102928180187252895806133)
          ·
            refine ⟨14259649516892554958981825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152102928180187252895806133 14259649516892554958981825)
            ·
              refine ⟨10694737137669416219236369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14259649516892554958981825 10694737137669416219236369)
              ·
                refine ⟨8021052853252062164427277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10694737137669416219236369 8021052853252062164427277)
                ·
                  refine ⟨3007894819969523311660229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8021052853252062164427277 3007894819969523311660229)
                  ·
                    refine ⟨563980278744285620936293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3007894819969523311660229 563980278744285620936293)
                    ·
                      rfl

theorem cell23_3295043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 4].length) (baseStart_3295043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295043 prefixEnd_3295043 := by exact prefixLift 3295043
  have htrace : WordTrace (prefixWord ++ tailWord_3295043) baseStart_3295043 baseEnd_3295043 := by
    simpa [prefixWord, tailWord_3295043, baseEnd_3295043] using wordTrace_append hprefix tailTrace_3295043
  have hstable : (prefixWord ++ tailWord_3295043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295043).length < 2 ^ (prefixWord ++ tailWord_3295043).sum := by decide
  have hdescent : baseEnd_3295043 < baseStart_3295043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295123 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 4, 6, 2]
def baseStart_3295123 : Nat := 118140960795 + 3295123 * 2 ^ 59
def prefixEnd_3295123 : Nat := 4983230072969 + 3 ^ 40 * 3295123 * 2
def baseEnd_3295123 : Nat := 1691981914685216549808511

theorem tailTrace_3295123 : CollatzResearch.WordTrace tailWord_3295123 prefixEnd_3295123 1691981914685216549808511 := by
  unfold tailWord_3295123
  simp only [CollatzResearch.WordTrace]
  refine ⟨120183009241339608049722023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80122006160893072033148015 120183009241339608049722023)
  ·
    refine ⟨180274513862009412074583035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120183009241339608049722023 180274513862009412074583035)
    ·
      refine ⟨270411770793014118111874553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180274513862009412074583035 270411770793014118111874553)
      ·
        refine ⟨202808828094760588583905915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270411770793014118111874553 202808828094760588583905915)
        ·
          refine ⟨304213242142140882875858873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202808828094760588583905915 304213242142140882875858873)
          ·
            refine ⟨228159931606605662156894155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304213242142140882875858873 228159931606605662156894155)
            ·
              refine ⟨342239897409908493235341233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228159931606605662156894155 342239897409908493235341233)
              ·
                refine ⟨256679923057431369926505925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342239897409908493235341233 256679923057431369926505925)
                ·
                  refine ⟨48127485573268381861219861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 256679923057431369926505925 48127485573268381861219861)
                  ·
                    refine ⟨2255975886246955399744681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48127485573268381861219861 2255975886246955399744681)
                    ·
                      refine ⟨1691981914685216549808511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2255975886246955399744681 1691981914685216549808511)
                      ·
                        rfl

theorem cell23_3295123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 6, 2].length) (baseStart_3295123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295123 prefixEnd_3295123 := by exact prefixLift 3295123
  have htrace : WordTrace (prefixWord ++ tailWord_3295123) baseStart_3295123 baseEnd_3295123 := by
    simpa [prefixWord, tailWord_3295123, baseEnd_3295123] using wordTrace_append hprefix tailTrace_3295123
  have hstable : (prefixWord ++ tailWord_3295123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295123).length < 2 ^ (prefixWord ++ tailWord_3295123).sum := by decide
  have hdescent : baseEnd_3295123 < baseStart_3295123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295128 : List Nat := [2, 1, 2, 6, 2, 1, 2, 2, 1, 4]
def baseStart_3295128 : Nat := 118140960795 + 3295128 * 2 ^ 59
def prefixEnd_3295128 : Nat := 4983230072969 + 3 ^ 40 * 3295128 * 2
def baseEnd_3295128 : Nat := 563994827362829676748663

theorem tailTrace_3295128 : CollatzResearch.WordTrace tailWord_3295128 prefixEnd_3295128 563994827362829676748663 := by
  unfold tailWord_3295128
  simp only [CollatzResearch.WordTrace]
  refine ⟨60091595803160746951827019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80122127737547662602436025 60091595803160746951827019)
  ·
    refine ⟨90137393704741120427740529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60091595803160746951827019 90137393704741120427740529)
    ·
      refine ⟨67603045278555840320805397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90137393704741120427740529 67603045278555840320805397)
      ·
        refine ⟨3168892747432305015037753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67603045278555840320805397 3168892747432305015037753)
        ·
          refine ⟨2376669560574228761278315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3168892747432305015037753 2376669560574228761278315)
          ·
            refine ⟨3565004340861343141917473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2376669560574228761278315 3565004340861343141917473)
            ·
              refine ⟨2673753255646007356438105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3565004340861343141917473 2673753255646007356438105)
              ·
                refine ⟨2005314941734505517328579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2673753255646007356438105 2005314941734505517328579)
                ·
                  refine ⟨3007972412601758275992869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2005314941734505517328579 3007972412601758275992869)
                  ·
                    refine ⟨563994827362829676748663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3007972412601758275992869 563994827362829676748663)
                    ·
                      rfl

theorem cell23_3295128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 1, 4].length) (baseStart_3295128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295128 prefixEnd_3295128 := by exact prefixLift 3295128
  have htrace : WordTrace (prefixWord ++ tailWord_3295128) baseStart_3295128 baseEnd_3295128 := by
    simpa [prefixWord, tailWord_3295128, baseEnd_3295128] using wordTrace_append hprefix tailTrace_3295128
  have hstable : (prefixWord ++ tailWord_3295128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295128).length < 2 ^ (prefixWord ++ tailWord_3295128).sum := by decide
  have hdescent : baseEnd_3295128 < baseStart_3295128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295157 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 5, 2, 2]
def baseStart_3295157 : Nat := 118140960795 + 3295157 * 2 ^ 59
def prefixEnd_3295157 : Nat := 4983230072969 + 3 ^ 40 * 3295157 * 2
def baseEnd_3295157 : Nat := 1691999373027469416783355

theorem tailTrace_3295157 : CollatzResearch.WordTrace tailWord_3295157 prefixEnd_3295157 1691999373027469416783355 := by
  unfold tailWord_3295157
  simp only [CollatzResearch.WordTrace]
  refine ⟨120184249323216431856459725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80122832882144287904306483 120184249323216431856459725)
  ·
    refine ⟨45069093496206161946172397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120184249323216431856459725 45069093496206161946172397)
    ·
      refine ⟨16900910061077310729814649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45069093496206161946172397 16900910061077310729814649)
      ·
        refine ⟨12675682545807983047360987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16900910061077310729814649 12675682545807983047360987)
        ·
          refine ⟨19013523818711974571041481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12675682545807983047360987 19013523818711974571041481)
          ·
            refine ⟨14260142864033980928281111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19013523818711974571041481 14260142864033980928281111)
            ·
              refine ⟨21390214296050971392421667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14260142864033980928281111 21390214296050971392421667)
              ·
                refine ⟨32085321444076457088632501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21390214296050971392421667 32085321444076457088632501)
                ·
                  refine ⟨3007998885382167852059297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32085321444076457088632501 3007998885382167852059297)
                  ·
                    refine ⟨2255999164036625889044473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3007998885382167852059297 2255999164036625889044473)
                    ·
                      refine ⟨1691999373027469416783355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2255999164036625889044473 1691999373027469416783355)
                      ·
                        rfl

theorem cell23_3295157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_3295157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295157 prefixEnd_3295157 := by exact prefixLift 3295157
  have htrace : WordTrace (prefixWord ++ tailWord_3295157) baseStart_3295157 baseEnd_3295157 := by
    simpa [prefixWord, tailWord_3295157, baseEnd_3295157] using wordTrace_append hprefix tailTrace_3295157
  have hstable : (prefixWord ++ tailWord_3295157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295157).length < 2 ^ (prefixWord ++ tailWord_3295157).sum := by decide
  have hdescent : baseEnd_3295157 < baseStart_3295157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295160 : List Nat := [2, 1, 2, 1, 2, 3, 2, 4, 1, 2, 3]
def baseStart_3295160 : Nat := 118140960795 + 3295160 * 2 ^ 59
def prefixEnd_3295160 : Nat := 4983230072969 + 3 ^ 40 * 3295160 * 2
def baseEnd_3295160 : Nat := 1692000913469432905045841

theorem tailTrace_3295160 : CollatzResearch.WordTrace tailWord_3295160 prefixEnd_3295160 1692000913469432905045841 := by
  unfold tailWord_3295160
  simp only [CollatzResearch.WordTrace]
  refine ⟨60092179371102781684409467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80122905828137042245879289 60092179371102781684409467)
  ·
    refine ⟨90138269056654172526614201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60092179371102781684409467 90138269056654172526614201)
    ·
      refine ⟨67603701792490629394960651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90138269056654172526614201 67603701792490629394960651)
      ·
        refine ⟨101405552688735944092440977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67603701792490629394960651 101405552688735944092440977)
        ·
          refine ⟨76054164516551958069330733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101405552688735944092440977 76054164516551958069330733)
          ·
            refine ⟨28520311693706984275999025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76054164516551958069330733 28520311693706984275999025)
            ·
              refine ⟨21390233770280238206999269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28520311693706984275999025 21390233770280238206999269)
              ·
                refine ⟨4010668831927544663812363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21390233770280238206999269 4010668831927544663812363)
                ·
                  refine ⟨6016003247891316995718545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4010668831927544663812363 6016003247891316995718545)
                  ·
                    refine ⟨4512002435918487746788909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6016003247891316995718545 4512002435918487746788909)
                    ·
                      refine ⟨1692000913469432905045841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4512002435918487746788909 1692000913469432905045841)
                      ·
                        rfl

theorem cell23_3295160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 1, 2, 3].length) (baseStart_3295160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295160 prefixEnd_3295160 := by exact prefixLift 3295160
  have htrace : WordTrace (prefixWord ++ tailWord_3295160) baseStart_3295160 baseEnd_3295160 := by
    simpa [prefixWord, tailWord_3295160, baseEnd_3295160] using wordTrace_append hprefix tailTrace_3295160
  have hstable : (prefixWord ++ tailWord_3295160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295160).length < 2 ^ (prefixWord ++ tailWord_3295160).sum := by decide
  have hdescent : baseEnd_3295160 < baseStart_3295160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295173 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 3, 3, 3]
def baseStart_3295173 : Nat := 118140960795 + 3295173 * 2 ^ 59
def prefixEnd_3295173 : Nat := 4983230072969 + 3 ^ 40 * 3295173 * 2
def baseEnd_3295173 : Nat := 1692007588717941354183281

theorem tailTrace_3295173 : CollatzResearch.WordTrace tailWord_3295173 prefixEnd_3295173 1692007588717941354183281 := by
  unfold tailWord_3295173
  simp only [CollatzResearch.WordTrace]
  refine ⟨120184832891158466589042173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80123221927438977726028115 120184832891158466589042173)
  ·
    refine ⟨45069312334184424970890815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120184832891158466589042173 45069312334184424970890815)
    ·
      refine ⟨67603968501276637456336223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45069312334184424970890815 67603968501276637456336223)
      ·
        refine ⟨101405952751914956184504335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67603968501276637456336223 101405952751914956184504335)
        ·
          refine ⟨152108929127872434276756503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101405952751914956184504335 152108929127872434276756503)
          ·
            refine ⟨228163393691808651415134755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152108929127872434276756503 228163393691808651415134755)
            ·
              refine ⟨342245090537712977122702133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228163393691808651415134755 342245090537712977122702133)
              ·
                refine ⟨32085477237910591605253325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 342245090537712977122702133 32085477237910591605253325)
                ·
                  refine ⟨12032053964216471851969997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32085477237910591605253325 12032053964216471851969997)
                  ·
                    refine ⟨4512020236581176944488749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12032053964216471851969997 4512020236581176944488749)
                    ·
                      refine ⟨1692007588717941354183281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4512020236581176944488749 1692007588717941354183281)
                      ·
                        rfl

theorem cell23_3295173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_3295173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295173 prefixEnd_3295173 := by exact prefixLift 3295173
  have htrace : WordTrace (prefixWord ++ tailWord_3295173) baseStart_3295173 baseEnd_3295173 := by
    simpa [prefixWord, tailWord_3295173, baseEnd_3295173] using wordTrace_append hprefix tailTrace_3295173
  have hstable : (prefixWord ++ tailWord_3295173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295173).length < 2 ^ (prefixWord ++ tailWord_3295173).sum := by decide
  have hdescent : baseEnd_3295173 < baseStart_3295173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295200 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 5, 3, 2]
def baseStart_3295200 : Nat := 118140960795 + 3295200 * 2 ^ 59
def prefixEnd_3295200 : Nat := 4983230072969 + 3 ^ 40 * 3295200 * 2
def baseEnd_3295200 : Nat := 1692021452695612748545657

theorem tailTrace_3295200 : CollatzResearch.WordTrace tailWord_3295200 prefixEnd_3295200 1692021452695612748545657 := by
  unfold tailWord_3295200
  simp only [CollatzResearch.WordTrace]
  refine ⟨60092908831030325100137527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80123878441373766800183369 60092908831030325100137527)
  ·
    refine ⟨90139363246545487650206291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60092908831030325100137527 90139363246545487650206291)
    ·
      refine ⟨135209044869818231475309437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90139363246545487650206291 135209044869818231475309437)
      ·
        refine ⟨50703391826181836803241039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135209044869818231475309437 50703391826181836803241039)
        ·
          refine ⟨76055087739272755204861559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50703391826181836803241039 76055087739272755204861559)
          ·
            refine ⟨114082631608909132807292339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76055087739272755204861559 114082631608909132807292339)
            ·
              refine ⟨171123947413363699210938509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114082631608909132807292339 171123947413363699210938509)
              ·
                refine ⟨64171480280011387204101941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171123947413363699210938509 64171480280011387204101941)
                ·
                  refine ⟨6016076276251067550384557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64171480280011387204101941 6016076276251067550384557)
                  ·
                    refine ⟨2256028603594150331394209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6016076276251067550384557 2256028603594150331394209)
                    ·
                      refine ⟨1692021452695612748545657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2256028603594150331394209 1692021452695612748545657)
                      ·
                        rfl

theorem cell23_3295200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_3295200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295200 prefixEnd_3295200 := by exact prefixLift 3295200
  have htrace : WordTrace (prefixWord ++ tailWord_3295200) baseStart_3295200 baseEnd_3295200 := by
    simpa [prefixWord, tailWord_3295200, baseEnd_3295200] using wordTrace_append hprefix tailTrace_3295200
  have hstable : (prefixWord ++ tailWord_3295200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295200).length < 2 ^ (prefixWord ++ tailWord_3295200).sum := by decide
  have hdescent : baseEnd_3295200 < baseStart_3295200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295268 : List Nat := [2, 3, 1, 4, 3, 1, 1, 2, 1, 3, 2]
def baseStart_3295268 : Nat := 118140960795 + 3295268 * 2 ^ 59
def prefixEnd_3295268 : Nat := 4983230072969 + 3 ^ 40 * 3295268 * 2
def baseEnd_3295268 : Nat := 1692056369380118482495345

theorem tailTrace_3295268 : CollatzResearch.WordTrace tailWord_3295268 prefixEnd_3295268 1692056369380118482495345 := by
  unfold tailWord_3295268
  simp only [CollatzResearch.WordTrace]
  refine ⟨60094148912907148906875229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80125531883876198542500305 60094148912907148906875229)
  ·
    refine ⟨22535305842340180840078211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60094148912907148906875229 22535305842340180840078211)
    ·
      refine ⟨33802958763510271260117317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22535305842340180840078211 33802958763510271260117317)
      ·
        refine ⟨6338054768158175861271997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33802958763510271260117317 6338054768158175861271997)
        ·
          refine ⟨2376770538059315947976999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6338054768158175861271997 2376770538059315947976999)
          ·
            refine ⟨3565155807088973921965499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2376770538059315947976999 3565155807088973921965499)
            ·
              refine ⟨5347733710633460882948249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3565155807088973921965499 5347733710633460882948249)
              ·
                refine ⟨4010800282975095662211187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5347733710633460882948249 4010800282975095662211187)
                ·
                  refine ⟨6016200424462643493316781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4010800282975095662211187 6016200424462643493316781)
                  ·
                    refine ⟨2256075159173491309993793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6016200424462643493316781 2256075159173491309993793)
                    ·
                      refine ⟨1692056369380118482495345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2256075159173491309993793 1692056369380118482495345)
                      ·
                        rfl

theorem cell23_3295268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_3295268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295268 prefixEnd_3295268 := by exact prefixLift 3295268
  have htrace : WordTrace (prefixWord ++ tailWord_3295268) baseStart_3295268 baseEnd_3295268 := by
    simpa [prefixWord, tailWord_3295268, baseEnd_3295268] using wordTrace_append hprefix tailTrace_3295268
  have hstable : (prefixWord ++ tailWord_3295268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295268).length < 2 ^ (prefixWord ++ tailWord_3295268).sum := by decide
  have hdescent : baseEnd_3295268 < baseStart_3295268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295283 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 1, 7]
def baseStart_3295283 : Nat := 118140960795 + 3295283 * 2 ^ 59
def prefixEnd_3295283 : Nat := 4983230072969 + 3 ^ 40 * 3295283 * 2
def baseEnd_3295283 : Nat := 564021357196645307935925

theorem tailTrace_3295283 : CollatzResearch.WordTrace tailWord_3295283 prefixEnd_3295283 564021357196645307935925 := by
  unfold tailWord_3295283
  simp only [CollatzResearch.WordTrace]
  refine ⟨120188844920759955375546503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80125896613839970250364335 120188844920759955375546503)
  ·
    refine ⟨180283267381139933063319755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120188844920759955375546503 180283267381139933063319755)
    ·
      refine ⟨270424901071709899594979633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180283267381139933063319755 270424901071709899594979633)
      ·
        refine ⟨202818675803782424696234725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270424901071709899594979633 202818675803782424696234725)
        ·
          refine ⟨38028501713209204630544011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202818675803782424696234725 38028501713209204630544011)
          ·
            refine ⟨57042752569813806945816017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38028501713209204630544011 57042752569813806945816017)
            ·
              refine ⟨42782064427360355209362013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57042752569813806945816017 42782064427360355209362013)
              ·
                refine ⟨16043274160260133203510755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42782064427360355209362013 16043274160260133203510755)
                ·
                  refine ⟨24064911240390199805266133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16043274160260133203510755 24064911240390199805266133)
                  ·
                    refine ⟨564021357196645307935925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24064911240390199805266133 564021357196645307935925)
                    ·
                      rfl

theorem cell23_3295283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 7].length) (baseStart_3295283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295283 prefixEnd_3295283 := by exact prefixLift 3295283
  have htrace : WordTrace (prefixWord ++ tailWord_3295283) baseStart_3295283 baseEnd_3295283 := by
    simpa [prefixWord, tailWord_3295283, baseEnd_3295283] using wordTrace_append hprefix tailTrace_3295283
  have hstable : (prefixWord ++ tailWord_3295283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295283).length < 2 ^ (prefixWord ++ tailWord_3295283).sum := by decide
  have hdescent : baseEnd_3295283 < baseStart_3295283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295310 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_3295310 : Nat := 118140960795 + 3295310 * 2 ^ 59
def prefixEnd_3295310 : Nat := 4983230072969 + 3 ^ 40 * 3295310 * 2
def baseEnd_3295310 : Nat := 1692077935567607318170151

theorem tailTrace_3295310 : CollatzResearch.WordTrace tailWord_3295310 prefixEnd_3295310 1692077935567607318170151 := by
  unfold tailWord_3295310
  simp only [CollatzResearch.WordTrace]
  refine ⟨15023728711457767373347423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80126553127774759324519589 15023728711457767373347423)
  ·
    refine ⟨22535593067186651060021135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15023728711457767373347423 22535593067186651060021135)
    ·
      refine ⟨33803389600779976590031703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22535593067186651060021135 33803389600779976590031703)
      ·
        refine ⟨50705084401169964885047555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33803389600779976590031703 50705084401169964885047555)
        ·
          refine ⟨76057626601754947327571333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50705084401169964885047555 76057626601754947327571333)
          ·
            refine ⟨14260804987829052623919625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76057626601754947327571333 14260804987829052623919625)
            ·
              refine ⟨10695603740871789467939719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14260804987829052623919625 10695603740871789467939719)
              ·
                refine ⟨16043405611307684201909579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10695603740871789467939719 16043405611307684201909579)
                ·
                  refine ⟨24065108416961526302864369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16043405611307684201909579 24065108416961526302864369)
                  ·
                    refine ⟨18048831312721144727148277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24065108416961526302864369 18048831312721144727148277)
                    ·
                      refine ⟨1692077935567607318170151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18048831312721144727148277 1692077935567607318170151)
                      ·
                        rfl

theorem cell23_3295310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_3295310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295310 prefixEnd_3295310 := by exact prefixLift 3295310
  have htrace : WordTrace (prefixWord ++ tailWord_3295310) baseStart_3295310 baseEnd_3295310 := by
    simpa [prefixWord, tailWord_3295310, baseEnd_3295310] using wordTrace_append hprefix tailTrace_3295310
  have hstable : (prefixWord ++ tailWord_3295310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295310).length < 2 ^ (prefixWord ++ tailWord_3295310).sum := by decide
  have hdescent : baseEnd_3295310 < baseStart_3295310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295313 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 2, 8]
def baseStart_3295313 : Nat := 118140960795 + 3295313 * 2 ^ 59
def prefixEnd_3295313 : Nat := 4983230072969 + 3 ^ 40 * 3295313 * 2
def baseEnd_3295313 : Nat := 564026492003190268810879

theorem tailTrace_3295313 : CollatzResearch.WordTrace tailWord_3295313 prefixEnd_3295313 564026492003190268810879 := by
  unfold tailWord_3295313
  simp only [CollatzResearch.WordTrace]
  refine ⟨120189939110651270499138593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80126626073767513666092395 120189939110651270499138593)
  ·
    refine ⟨90142454332988452874353945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120189939110651270499138593 90142454332988452874353945)
    ·
      refine ⟨67606840749741339655765459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90142454332988452874353945 67606840749741339655765459)
      ·
        refine ⟨101410261124612009483648189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67606840749741339655765459 101410261124612009483648189)
        ·
          refine ⟨38028847921729503556368071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101410261124612009483648189 38028847921729503556368071)
          ·
            refine ⟨57043271882594255334552107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38028847921729503556368071 57043271882594255334552107)
            ·
              refine ⟨85564907823891383001828161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57043271882594255334552107 85564907823891383001828161)
              ·
                refine ⟨64173680867918537251371121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85564907823891383001828161 64173680867918537251371121)
                ·
                  refine ⟨48130260650938902938528341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64173680867918537251371121 48130260650938902938528341)
                  ·
                    refine ⟨564026492003190268810879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48130260650938902938528341 564026492003190268810879)
                    ·
                      rfl

theorem cell23_3295313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_3295313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295313 prefixEnd_3295313 := by exact prefixLift 3295313
  have htrace : WordTrace (prefixWord ++ tailWord_3295313) baseStart_3295313 baseEnd_3295313 := by
    simpa [prefixWord, tailWord_3295313, baseEnd_3295313] using wordTrace_append hprefix tailTrace_3295313
  have hstable : (prefixWord ++ tailWord_3295313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295313).length < 2 ^ (prefixWord ++ tailWord_3295313).sum := by decide
  have hdescent : baseEnd_3295313 < baseStart_3295313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295364 : List Nat := [2, 3, 2, 1, 2, 1, 1, 6, 1, 4]
def baseStart_3295364 : Nat := 118140960795 + 3295364 * 2 ^ 59
def prefixEnd_3295364 : Nat := 4983230072969 + 3 ^ 40 * 3295364 * 2
def baseEnd_3295364 : Nat := 564035221174316702298301

theorem tailTrace_3295364 : CollatzResearch.WordTrace tailWord_3295364 prefixEnd_3295364 564035221174316702298301 := by
  unfold tailWord_3295364
  simp only [CollatzResearch.WordTrace]
  refine ⟨60095899616733253104622573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80127866155644337472830097 60095899616733253104622573)
  ·
    refine ⟨22535962356274969914233465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60095899616733253104622573 22535962356274969914233465)
    ·
      refine ⟨16901971767206227435675099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22535962356274969914233465 16901971767206227435675099)
      ·
        refine ⟨25352957650809341153512649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16901971767206227435675099 25352957650809341153512649)
        ·
          refine ⟨19014718238107005865134487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25352957650809341153512649 19014718238107005865134487)
          ·
            refine ⟨28522077357160508797701731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19014718238107005865134487 28522077357160508797701731)
            ·
              refine ⟨42783116035740763196552597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28522077357160508797701731 42783116035740763196552597)
              ·
                refine ⟨2005458564175348274838403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42783116035740763196552597 2005458564175348274838403)
                ·
                  refine ⟨3008187846263022412257605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2005458564175348274838403 3008187846263022412257605)
                  ·
                    refine ⟨564035221174316702298301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3008187846263022412257605 564035221174316702298301)
                    ·
                      rfl

theorem cell23_3295364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_3295364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295364 prefixEnd_3295364 := by exact prefixLift 3295364
  have htrace : WordTrace (prefixWord ++ tailWord_3295364) baseStart_3295364 baseEnd_3295364 := by
    simpa [prefixWord, tailWord_3295364, baseEnd_3295364] using wordTrace_append hprefix tailTrace_3295364
  have hstable : (prefixWord ++ tailWord_3295364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295364).length < 2 ^ (prefixWord ++ tailWord_3295364).sum := by decide
  have hdescent : baseEnd_3295364 < baseStart_3295364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295387 : List Nat := [1, 1, 1, 1, 1, 1, 2, 8, 3, 1, 3]
def baseStart_3295387 : Nat := 118140960795 + 3295387 * 2 ^ 59
def prefixEnd_3295387 : Nat := 4983230072969 + 3 ^ 40 * 3295387 * 2
def baseEnd_3295387 : Nat := 1692117473578003516907297

theorem tailTrace_3295387 : CollatzResearch.WordTrace tailWord_3295387 prefixEnd_3295387 1692117473578003516907297 := by
  unfold tailWord_3295387
  simp only [CollatzResearch.WordTrace]
  refine ⟨120192638112383181137332415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80128425408255454091554943 120192638112383181137332415)
  ·
    refine ⟨180288957168574771705998623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120192638112383181137332415 180288957168574771705998623)
    ·
      refine ⟨270433435752862157558997935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180288957168574771705998623 270433435752862157558997935)
      ·
        refine ⟨405650153629293236338496903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270433435752862157558997935 405650153629293236338496903)
        ·
          refine ⟨608475230443939854507745355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405650153629293236338496903 608475230443939854507745355)
          ·
            refine ⟨912712845665909781761618033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608475230443939854507745355 912712845665909781761618033)
            ·
              refine ⟨684534634249432336321213525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 912712845665909781761618033 684534634249432336321213525)
              ·
                refine ⟨8021890245110535191264221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 684534634249432336321213525 8021890245110535191264221)
                ·
                  refine ⟨3008208841916450696724083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8021890245110535191264221 3008208841916450696724083)
                  ·
                    refine ⟨4512313262874676045086125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3008208841916450696724083 4512313262874676045086125)
                    ·
                      refine ⟨1692117473578003516907297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4512313262874676045086125 1692117473578003516907297)
                      ·
                        rfl

theorem cell23_3295387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 1, 3].length) (baseStart_3295387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295387 prefixEnd_3295387 := by exact prefixLift 3295387
  have htrace : WordTrace (prefixWord ++ tailWord_3295387) baseStart_3295387 baseEnd_3295387 := by
    simpa [prefixWord, tailWord_3295387, baseEnd_3295387] using wordTrace_append hprefix tailTrace_3295387
  have hstable : (prefixWord ++ tailWord_3295387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295387).length < 2 ^ (prefixWord ++ tailWord_3295387).sum := by decide
  have hdescent : baseEnd_3295387 < baseStart_3295387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295397 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 1, 5, 2]
def baseStart_3295397 : Nat := 118140960795 + 3295397 * 2 ^ 59
def prefixEnd_3295397 : Nat := 4983230072969 + 3 ^ 40 * 3295397 * 2
def baseEnd_3295397 : Nat := 1692122608384548477782251

theorem tailTrace_3295397 : CollatzResearch.WordTrace tailWord_3295397 prefixEnd_3295397 1692122608384548477782251 := by
  unfold tailWord_3295397
  simp only [CollatzResearch.WordTrace]
  refine ⟨120193002842346952845196445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80128668561564635230130963 120193002842346952845196445)
  ·
    refine ⟨45072376065880107316948667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120193002842346952845196445 45072376065880107316948667)
    ·
      refine ⟨67608564098820160975423001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45072376065880107316948667 67608564098820160975423001)
      ·
        refine ⟨50706423074115120731567251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67608564098820160975423001 50706423074115120731567251)
        ·
          refine ⟨76059634611172681097350877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50706423074115120731567251 76059634611172681097350877)
          ·
            refine ⟨28522362979189755411506579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76059634611172681097350877 28522362979189755411506579)
            ·
              refine ⟨42783544468784633117259869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28522362979189755411506579 42783544468784633117259869)
              ·
                refine ⟨16043829175794237418972451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42783544468784633117259869 16043829175794237418972451)
                ·
                  refine ⟨24065743763691356128458677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16043829175794237418972451 24065743763691356128458677)
                  ·
                    refine ⟨2256163477846064637043001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24065743763691356128458677 2256163477846064637043001)
                    ·
                      refine ⟨1692122608384548477782251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2256163477846064637043001 1692122608384548477782251)
                      ·
                        rfl

theorem cell23_3295397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_3295397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295397 prefixEnd_3295397 := by exact prefixLift 3295397
  have htrace : WordTrace (prefixWord ++ tailWord_3295397) baseStart_3295397 baseEnd_3295397 := by
    simpa [prefixWord, tailWord_3295397, baseEnd_3295397] using wordTrace_append hprefix tailTrace_3295397
  have hstable : (prefixWord ++ tailWord_3295397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295397).length < 2 ^ (prefixWord ++ tailWord_3295397).sum := by decide
  have hdescent : baseEnd_3295397 < baseStart_3295397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295440 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 4]
def baseStart_3295440 : Nat := 118140960795 + 3295440 * 2 ^ 59
def prefixEnd_3295440 : Nat := 4983230072969 + 3 ^ 40 * 3295440 * 2
def baseEnd_3295440 : Nat := 1692144688052691809544553

theorem tailTrace_3295440 : CollatzResearch.WordTrace tailWord_3295440 prefixEnd_3295440 1692144688052691809544553 := by
  unfold tailWord_3295440
  simp only [CollatzResearch.WordTrace]
  refine ⟨60097285590595585594505887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80129714120794114126007849 60097285590595585594505887)
  ·
    refine ⟨90145928385893378391758831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60097285590595585594505887 90145928385893378391758831)
    ·
      refine ⟨135218892578840067587638247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90145928385893378391758831 135218892578840067587638247)
      ·
        refine ⟨202828338868260101381457371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135218892578840067587638247 202828338868260101381457371)
        ·
          refine ⟨304242508302390152072186057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202828338868260101381457371 304242508302390152072186057)
          ·
            refine ⟨228181881226792614054139543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304242508302390152072186057 228181881226792614054139543)
            ·
              refine ⟨342272821840188921081209315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228181881226792614054139543 342272821840188921081209315)
              ·
                refine ⟨513409232760283381621813973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342272821840188921081209315 513409232760283381621813973)
                ·
                  refine ⟨12033028892819141756761265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 513409232760283381621813973 12033028892819141756761265)
                  ·
                    refine ⟨9024771669614356317570949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12033028892819141756761265 9024771669614356317570949)
                    ·
                      refine ⟨1692144688052691809544553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9024771669614356317570949 1692144688052691809544553)
                      ·
                        rfl

theorem cell23_3295440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_3295440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295440 prefixEnd_3295440 := by exact prefixLift 3295440
  have htrace : WordTrace (prefixWord ++ tailWord_3295440) baseStart_3295440 baseEnd_3295440 := by
    simpa [prefixWord, tailWord_3295440, baseEnd_3295440] using wordTrace_append hprefix tailTrace_3295440
  have hstable : (prefixWord ++ tailWord_3295440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295440).length < 2 ^ (prefixWord ++ tailWord_3295440).sum := by decide
  have hdescent : baseEnd_3295440 < baseStart_3295440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295450 : List Nat := [3, 1, 1, 2, 2, 1, 4, 9]
def baseStart_3295450 : Nat := 118140960795 + 3295450 * 2 ^ 59
def prefixEnd_3295450 : Nat := 4983230072969 + 3 ^ 40 * 3295450 * 2
def baseEnd_3295450 : Nat := 62672215661453213719241

theorem tailTrace_3295450 : CollatzResearch.WordTrace tailWord_3295450 prefixEnd_3295450 62672215661453213719241 := by
  unfold tailWord_3295450
  simp only [CollatzResearch.WordTrace]
  refine ⟨30048733977788735724218951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80129957274103295264583869 30048733977788735724218951)
  ·
    refine ⟨45073100966683103586328427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30048733977788735724218951 45073100966683103586328427)
    ·
      refine ⟨67609651450024655379492641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45073100966683103586328427 67609651450024655379492641)
      ·
        refine ⟨50707238587518491534619481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67609651450024655379492641 50707238587518491534619481)
        ·
          refine ⟨38030428940638868650964611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50707238587518491534619481 38030428940638868650964611)
          ·
            refine ⟨57045643410958302976446917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38030428940638868650964611 57045643410958302976446917)
            ·
              refine ⟨10696058139554681808083797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57045643410958302976446917 10696058139554681808083797)
              ·
                refine ⟨62672215661453213719241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10696058139554681808083797 62672215661453213719241)
                ·
                  rfl

theorem cell23_3295450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 9].length) (baseStart_3295450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295450 prefixEnd_3295450 := by exact prefixLift 3295450
  have htrace : WordTrace (prefixWord ++ tailWord_3295450) baseStart_3295450 baseEnd_3295450 := by
    simpa [prefixWord, tailWord_3295450, baseEnd_3295450] using wordTrace_append hprefix tailTrace_3295450
  have hstable : (prefixWord ++ tailWord_3295450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295450).length < 2 ^ (prefixWord ++ tailWord_3295450).sum := by decide
  have hdescent : baseEnd_3295450 < baseStart_3295450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295457 : List Nat := [1, 2, 3, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_3295457 : Nat := 118140960795 + 3295457 * 2 ^ 59
def prefixEnd_3295457 : Nat := 4983230072969 + 3 ^ 40 * 3295457 * 2
def baseEnd_3295457 : Nat := 1692153417223818243031975

theorem tailTrace_3295457 : CollatzResearch.WordTrace tailWord_3295457 prefixEnd_3295457 1692153417223818243031975 := by
  unfold tailWord_3295457
  simp only [CollatzResearch.WordTrace]
  refine ⟨120195191222129583092380625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80130127481419722061587083 120195191222129583092380625)
  ·
    refine ⟨90146393416597187319285469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120195191222129583092380625 90146393416597187319285469)
    ·
      refine ⟨33804897531223945244732051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90146393416597187319285469 33804897531223945244732051)
      ·
        refine ⟨50707346296835917867098077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33804897531223945244732051 50707346296835917867098077)
        ·
          refine ⟨19015254861313469200161779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50707346296835917867098077 19015254861313469200161779)
          ·
            refine ⟨28522882291970203800242669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19015254861313469200161779 28522882291970203800242669)
            ·
              refine ⟨10696080859488826425091001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28522882291970203800242669 10696080859488826425091001)
              ·
                refine ⟨8022060644616619818818251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10696080859488826425091001 8022060644616619818818251)
                ·
                  refine ⟨12033090966924929728227377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8022060644616619818818251 12033090966924929728227377)
                  ·
                    refine ⟨9024818225193697296170533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12033090966924929728227377 9024818225193697296170533)
                    ·
                      refine ⟨1692153417223818243031975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9024818225193697296170533 1692153417223818243031975)
                      ·
                        rfl

theorem cell23_3295457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_3295457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295457 prefixEnd_3295457 := by exact prefixLift 3295457
  have htrace : WordTrace (prefixWord ++ tailWord_3295457) baseStart_3295457 baseEnd_3295457 := by
    simpa [prefixWord, tailWord_3295457, baseEnd_3295457] using wordTrace_append hprefix tailTrace_3295457
  have hstable : (prefixWord ++ tailWord_3295457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295457).length < 2 ^ (prefixWord ++ tailWord_3295457).sum := by decide
  have hdescent : baseEnd_3295457 < baseStart_3295457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295461 : List Nat := [1, 3, 1, 4, 2, 2, 3, 1, 1, 1, 4]
def baseStart_3295461 : Nat := 118140960795 + 3295461 * 2 ^ 59
def prefixEnd_3295461 : Nat := 4983230072969 + 3 ^ 40 * 3295461 * 2
def baseEnd_3295461 : Nat := 1692155471146436227381957

theorem tailTrace_3295461 : CollatzResearch.WordTrace tailWord_3295461 prefixEnd_3295461 1692155471146436227381957 := by
  unfold tailWord_3295461
  simp only [CollatzResearch.WordTrace]
  refine ⟨120195337114115091775526237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80130224742743394517017491 120195337114115091775526237)
  ·
    refine ⟨45073251417793159415822339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120195337114115091775526237 45073251417793159415822339)
    ·
      refine ⟨67609877126689739123733509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45073251417793159415822339 67609877126689739123733509)
      ·
        refine ⟨12676851961254326085700033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67609877126689739123733509 12676851961254326085700033)
        ·
          refine ⟨9507638970940744564275025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12676851961254326085700033 9507638970940744564275025)
          ·
            refine ⟨7130729228205558423206269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9507638970940744564275025 7130729228205558423206269)
            ·
              refine ⟨2674023460577084408702351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7130729228205558423206269 2674023460577084408702351)
              ·
                refine ⟨4011035190865626613053527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2674023460577084408702351 4011035190865626613053527)
                ·
                  refine ⟨6016552786298439919580291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4011035190865626613053527 6016552786298439919580291)
                  ·
                    refine ⟨9024829179447659879370437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6016552786298439919580291 9024829179447659879370437)
                    ·
                      refine ⟨1692155471146436227381957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9024829179447659879370437 1692155471146436227381957)
                      ·
                        rfl

theorem cell23_3295461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_3295461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295461 prefixEnd_3295461 := by exact prefixLift 3295461
  have htrace : WordTrace (prefixWord ++ tailWord_3295461) baseStart_3295461 baseEnd_3295461 := by
    simpa [prefixWord, tailWord_3295461, baseEnd_3295461] using wordTrace_append hprefix tailTrace_3295461
  have hstable : (prefixWord ++ tailWord_3295461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295461).length < 2 ^ (prefixWord ++ tailWord_3295461).sum := by decide
  have hdescent : baseEnd_3295461 < baseStart_3295461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295464 : List Nat := [2, 1, 4, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_3295464 : Nat := 118140960795 + 3295464 * 2 ^ 59
def prefixEnd_3295464 : Nat := 4983230072969 + 3 ^ 40 * 3295464 * 2
def baseEnd_3295464 : Nat := 1692157011588399715644443

theorem tailTrace_3295464 : CollatzResearch.WordTrace tailWord_3295464 prefixEnd_3295464 1692157011588399715644443 := by
  unfold tailWord_3295464
  simp only [CollatzResearch.WordTrace]
  refine ⟨60097723266552111643942723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80130297688736148858590297 60097723266552111643942723)
  ·
    refine ⟨90146584899828167465914085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60097723266552111643942723 90146584899828167465914085)
    ·
      refine ⟨16902484668717781399858891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90146584899828167465914085 16902484668717781399858891)
      ·
        refine ⟨25353727003076672099788337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16902484668717781399858891 25353727003076672099788337)
        ·
          refine ⟨19015295252307504074841253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25353727003076672099788337 19015295252307504074841253)
          ·
            refine ⟨3565367859807657014032735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19015295252307504074841253 3565367859807657014032735)
            ·
              refine ⟨5348051789711485521049103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3565367859807657014032735 5348051789711485521049103)
              ·
                refine ⟨8022077684567228281573655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5348051789711485521049103 8022077684567228281573655)
                ·
                  refine ⟨12033116526850842422360483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8022077684567228281573655 12033116526850842422360483)
                  ·
                    refine ⟨18049674790276263633540725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12033116526850842422360483 18049674790276263633540725)
                    ·
                      refine ⟨1692157011588399715644443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18049674790276263633540725 1692157011588399715644443)
                      ·
                        rfl

theorem cell23_3295464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_3295464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295464 prefixEnd_3295464 := by exact prefixLift 3295464
  have htrace : WordTrace (prefixWord ++ tailWord_3295464) baseStart_3295464 baseEnd_3295464 := by
    simpa [prefixWord, tailWord_3295464, baseEnd_3295464] using wordTrace_append hprefix tailTrace_3295464
  have hstable : (prefixWord ++ tailWord_3295464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295464).length < 2 ^ (prefixWord ++ tailWord_3295464).sum := by decide
  have hdescent : baseEnd_3295464 < baseStart_3295464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295567 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 3]
def baseStart_3295567 : Nat := 118140960795 + 3295567 * 2 ^ 59
def prefixEnd_3295567 : Nat := 4983230072969 + 3 ^ 40 * 3295567 * 2
def baseEnd_3295567 : Nat := 1692209900095812812656469

theorem tailTrace_3295567 : CollatzResearch.WordTrace tailWord_3295567 prefixEnd_3295567 1692209900095812812656469 := by
  unfold tailWord_3295567
  simp only [CollatzResearch.WordTrace]
  refine ⟨120199203251731071878884955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80132802167820714585923303 120199203251731071878884955)
  ·
    refine ⟨180298804877596607818327433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120199203251731071878884955 180298804877596607818327433)
    ·
      refine ⟨135224103658197455863745575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180298804877596607818327433 135224103658197455863745575)
      ·
        refine ⟨202836155487296183795618363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135224103658197455863745575 202836155487296183795618363)
        ·
          refine ⟨304254233230944275693427545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202836155487296183795618363 304254233230944275693427545)
          ·
            refine ⟨228190674923208206770070659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304254233230944275693427545 228190674923208206770070659)
            ·
              refine ⟨342286012384812310155105989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228190674923208206770070659 342286012384812310155105989)
              ·
                refine ⟨64178627322152308154082373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 342286012384812310155105989 64178627322152308154082373)
                ·
                  refine ⟨12033492622903557778890445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64178627322152308154082373 12033492622903557778890445)
                  ·
                    refine ⟨4512559733588834167083917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12033492622903557778890445 4512559733588834167083917)
                    ·
                      refine ⟨1692209900095812812656469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4512559733588834167083917 1692209900095812812656469)
                      ·
                        rfl

theorem cell23_3295567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 3].length) (baseStart_3295567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295567 prefixEnd_3295567 := by exact prefixLift 3295567
  have htrace : WordTrace (prefixWord ++ tailWord_3295567) baseStart_3295567 baseEnd_3295567 := by
    simpa [prefixWord, tailWord_3295567, baseEnd_3295567] using wordTrace_append hprefix tailTrace_3295567
  have hstable : (prefixWord ++ tailWord_3295567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295567).length < 2 ^ (prefixWord ++ tailWord_3295567).sum := by decide
  have hdescent : baseEnd_3295567 < baseStart_3295567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295607 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 4]
def baseStart_3295607 : Nat := 118140960795 + 3295607 * 2 ^ 59
def prefixEnd_3295607 : Nat := 4983230072969 + 3 ^ 40 * 3295607 * 2
def baseEnd_3295607 : Nat := 1692230439321992656156285

theorem tailTrace_3295607 : CollatzResearch.WordTrace tailWord_3295607 prefixEnd_3295607 1692230439321992656156285 := by
  unfold tailWord_3295607
  simp only [CollatzResearch.WordTrace]
  refine ⟨120200662171586158710341075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80133774781057439140227383 120200662171586158710341075)
  ·
    refine ⟨180300993257379238065511613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120200662171586158710341075 180300993257379238065511613)
    ·
      refine ⟨67612872471517214274566855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180300993257379238065511613 67612872471517214274566855)
      ·
        refine ⟨101419308707275821411850283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67612872471517214274566855 101419308707275821411850283)
        ·
          refine ⟨152128963060913732117775425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101419308707275821411850283 152128963060913732117775425)
          ·
            refine ⟨114096722295685299088331569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152128963060913732117775425 114096722295685299088331569)
            ·
              refine ⟨85572541721763974316248677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114096722295685299088331569 85572541721763974316248677)
              ·
                refine ⟨16044851572830745184296627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85572541721763974316248677 16044851572830745184296627)
                ·
                  refine ⟨24067277359246117776444941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16044851572830745184296627 24067277359246117776444941)
                  ·
                    refine ⟨9025229009717294166166853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24067277359246117776444941 9025229009717294166166853)
                    ·
                      refine ⟨1692230439321992656156285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9025229009717294166166853 1692230439321992656156285)
                      ·
                        rfl

theorem cell23_3295607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_3295607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295607 prefixEnd_3295607 := by exact prefixLift 3295607
  have htrace : WordTrace (prefixWord ++ tailWord_3295607) baseStart_3295607 baseEnd_3295607 := by
    simpa [prefixWord, tailWord_3295607, baseEnd_3295607] using wordTrace_append hprefix tailTrace_3295607
  have hstable : (prefixWord ++ tailWord_3295607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295607).length < 2 ^ (prefixWord ++ tailWord_3295607).sum := by decide
  have hdescent : baseEnd_3295607 < baseStart_3295607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295637 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_3295637 : Nat := 118140960795 + 3295637 * 2 ^ 59
def prefixEnd_3295637 : Nat := 4983230072969 + 3 ^ 40 * 3295637 * 2
def baseEnd_3295637 : Nat := 1692245843741627538781147

theorem tailTrace_3295637 : CollatzResearch.WordTrace tailWord_3295637 prefixEnd_3295637 1692245843741627538781147 := by
  unfold tailWord_3295637
  simp only [CollatzResearch.WordTrace]
  refine ⟨120201756361477473833933165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80134504240984982555955443 120201756361477473833933165)
  ·
    refine ⟨45075658635554052687724937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120201756361477473833933165 45075658635554052687724937)
    ·
      refine ⟨33806743976665539515793703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45075658635554052687724937 33806743976665539515793703)
      ·
        refine ⟨50710115964998309273690555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33806743976665539515793703 50710115964998309273690555)
        ·
          refine ⟨76065173947497463910535833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50710115964998309273690555 76065173947497463910535833)
          ·
            refine ⟨57048880460623097932901875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76065173947497463910535833 57048880460623097932901875)
            ·
              refine ⟨85573320690934646899352813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57048880460623097932901875 85573320690934646899352813)
              ·
                refine ⟨32089995259100492587257305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85573320690934646899352813 32089995259100492587257305)
                ·
                  refine ⟨24067496444325369440442979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32089995259100492587257305 24067496444325369440442979)
                  ·
                    refine ⟨36101244666488054160664469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24067496444325369440442979 36101244666488054160664469)
                    ·
                      refine ⟨1692245843741627538781147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36101244666488054160664469 1692245843741627538781147)
                      ·
                        rfl

theorem cell23_3295637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_3295637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295637 prefixEnd_3295637 := by exact prefixLift 3295637
  have htrace : WordTrace (prefixWord ++ tailWord_3295637) baseStart_3295637 baseEnd_3295637 := by
    simpa [prefixWord, tailWord_3295637, baseEnd_3295637] using wordTrace_append hprefix tailTrace_3295637
  have hstable : (prefixWord ++ tailWord_3295637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295637).length < 2 ^ (prefixWord ++ tailWord_3295637).sum := by decide
  have hdescent : baseEnd_3295637 < baseStart_3295637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295731 : List Nat := [1, 1, 1, 2, 2, 2, 6, 2, 1, 1, 4]
def baseStart_3295731 : Nat := 118140960795 + 3295731 * 2 ^ 59
def prefixEnd_3295731 : Nat := 4983230072969 + 3 ^ 40 * 3295731 * 2
def baseEnd_3295731 : Nat := 1692294110923150171005715

theorem tailTrace_3295731 : CollatzResearch.WordTrace tailWord_3295731 prefixEnd_3295731 1692294110923150171005715 := by
  unfold tailWord_3295731
  simp only [CollatzResearch.WordTrace]
  refine ⟨120205184823136927887855047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80136789882091285258570031 120205184823136927887855047)
  ·
    refine ⟨180307777234705391831782571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120205184823136927887855047 180307777234705391831782571)
    ·
      refine ⟨270461665852058087747673857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180307777234705391831782571 270461665852058087747673857)
      ·
        refine ⟨202846249389043565810755393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270461665852058087747673857 202846249389043565810755393)
        ·
          refine ⟨152134687041782674358066545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202846249389043565810755393 152134687041782674358066545)
          ·
            refine ⟨114101015281337005768549909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152134687041782674358066545 114101015281337005768549909)
            ·
              refine ⟨5348485091312672145400777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114101015281337005768549909 5348485091312672145400777)
              ·
                refine ⟨4011363818484504109050583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5348485091312672145400777 4011363818484504109050583)
                ·
                  refine ⟨6017045727726756163575875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4011363818484504109050583 6017045727726756163575875)
                  ·
                    refine ⟨9025568591590134245363813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6017045727726756163575875 9025568591590134245363813)
                    ·
                      refine ⟨1692294110923150171005715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9025568591590134245363813 1692294110923150171005715)
                      ·
                        rfl

theorem cell23_3295731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 1, 4].length) (baseStart_3295731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295731 prefixEnd_3295731 := by exact prefixLift 3295731
  have htrace : WordTrace (prefixWord ++ tailWord_3295731) baseStart_3295731 baseEnd_3295731 := by
    simpa [prefixWord, tailWord_3295731, baseEnd_3295731] using wordTrace_append hprefix tailTrace_3295731
  have hstable : (prefixWord ++ tailWord_3295731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295731).length < 2 ^ (prefixWord ++ tailWord_3295731).sum := by decide
  have hdescent : baseEnd_3295731 < baseStart_3295731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295748 : List Nat := [2, 3, 2, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_3295748 : Nat := 118140960795 + 3295748 * 2 ^ 59
def prefixEnd_3295748 : Nat := 4983230072969 + 3 ^ 40 * 3295748 * 2
def baseEnd_3295748 : Nat := 1692302840094276604493137

theorem tailTrace_3295748 : CollatzResearch.WordTrace tailWord_3295748 prefixEnd_3295748 1692302840094276604493137 := by
  unfold tailWord_3295748
  simp only [CollatzResearch.WordTrace]
  refine ⟨60102902432037669895611949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80137203242716893194149265 60102902432037669895611949)
  ·
    refine ⟨22538588412014126210854481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60102902432037669895611949 22538588412014126210854481)
    ·
      refine ⟨16903941309010594658140861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22538588412014126210854481 16903941309010594658140861)
      ·
        refine ⟨6338977990878972996802823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16903941309010594658140861 6338977990878972996802823)
        ·
          refine ⟨9508466986318459495204235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6338977990878972996802823 9508466986318459495204235)
          ·
            refine ⟨14262700479477689242806353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9508466986318459495204235 14262700479477689242806353)
            ·
              refine ⟨10697025359608266932104765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14262700479477689242806353 10697025359608266932104765)
              ·
                refine ⟨4011384509853100099539287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10697025359608266932104765 4011384509853100099539287)
                ·
                  refine ⟨6017076764779650149308931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4011384509853100099539287 6017076764779650149308931)
                  ·
                    refine ⟨9025615147169475223963397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6017076764779650149308931 9025615147169475223963397)
                    ·
                      refine ⟨1692302840094276604493137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9025615147169475223963397 1692302840094276604493137)
                      ·
                        rfl

theorem cell23_3295748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_3295748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295748 prefixEnd_3295748 := by exact prefixLift 3295748
  have htrace : WordTrace (prefixWord ++ tailWord_3295748) baseStart_3295748 baseEnd_3295748 := by
    simpa [prefixWord, tailWord_3295748, baseEnd_3295748] using wordTrace_append hprefix tailTrace_3295748
  have hstable : (prefixWord ++ tailWord_3295748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295748).length < 2 ^ (prefixWord ++ tailWord_3295748).sum := by decide
  have hdescent : baseEnd_3295748 < baseStart_3295748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295794 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_3295794 : Nat := 118140960795 + 3295794 * 2 ^ 59
def prefixEnd_3295794 : Nat := 4983230072969 + 3 ^ 40 * 3295794 * 2
def baseEnd_3295794 : Nat := 1692326460204383424517925

theorem tailTrace_3295794 : CollatzResearch.WordTrace tailWord_3295794 prefixEnd_3295794 1692326460204383424517925 := by
  unfold tailWord_3295794
  simp only [CollatzResearch.WordTrace]
  refine ⟨30051870655477172411849609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80138321747939126431598957 30051870655477172411849609)
  ·
    refine ⟨22538902991607879308887207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30051870655477172411849609 22538902991607879308887207)
    ·
      refine ⟨33808354487411818963330811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22538902991607879308887207 33808354487411818963330811)
      ·
        refine ⟨50712531731117728444996217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33808354487411818963330811 50712531731117728444996217)
        ·
          refine ⟨38034398798338296333747163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50712531731117728444996217 38034398798338296333747163)
          ·
            refine ⟨57051598197507444500620745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38034398798338296333747163 57051598197507444500620745)
            ·
              refine ⟨42788698648130583375465559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57051598197507444500620745 42788698648130583375465559)
              ·
                refine ⟨64183047972195875063198339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42788698648130583375465559 64183047972195875063198339)
                ·
                  refine ⟨96274571958293812594797509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64183047972195875063198339 96274571958293812594797509)
                  ·
                    refine ⟨18051482242180089861524533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96274571958293812594797509 18051482242180089861524533)
                    ·
                      refine ⟨1692326460204383424517925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18051482242180089861524533 1692326460204383424517925)
                      ·
                        rfl

theorem cell23_3295794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_3295794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295794 prefixEnd_3295794 := by exact prefixLift 3295794
  have htrace : WordTrace (prefixWord ++ tailWord_3295794) baseStart_3295794 baseEnd_3295794 := by
    simpa [prefixWord, tailWord_3295794, baseEnd_3295794] using wordTrace_append hprefix tailTrace_3295794
  have hstable : (prefixWord ++ tailWord_3295794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295794).length < 2 ^ (prefixWord ++ tailWord_3295794).sum := by decide
  have hdescent : baseEnd_3295794 < baseStart_3295794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295798 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_3295798 : Nat := 118140960795 + 3295798 * 2 ^ 59
def prefixEnd_3295798 : Nat := 4983230072969 + 3 ^ 40 * 3295798 * 2
def baseEnd_3295798 : Nat := 1692328514127001408867907

theorem tailTrace_3295798 : CollatzResearch.WordTrace tailWord_3295798 prefixEnd_3295798 1692328514127001408867907 := by
  unfold tailWord_3295798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7512976782118387395659003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80138419009262798887029365 7512976782118387395659003)
  ·
    refine ⟨11269465173177581093488505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7512976782118387395659003 11269465173177581093488505)
    ·
      refine ⟨8452098879883185820116379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11269465173177581093488505 8452098879883185820116379)
      ·
        refine ⟨12678148319824778730174569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8452098879883185820116379 12678148319824778730174569)
        ·
          refine ⟨9508611239868584047630927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12678148319824778730174569 9508611239868584047630927)
          ·
            refine ⟨14262916859802876071446391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9508611239868584047630927 14262916859802876071446391)
            ·
              refine ⟨21394375289704314107169587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14262916859802876071446391 21394375289704314107169587)
              ·
                refine ⟨32091562934556471160754381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21394375289704314107169587 32091562934556471160754381)
                ·
                  refine ⟨12034336100458676685282893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32091562934556471160754381 12034336100458676685282893)
                  ·
                    refine ⟨4512876037672003756981085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12034336100458676685282893 4512876037672003756981085)
                    ·
                      refine ⟨1692328514127001408867907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4512876037672003756981085 1692328514127001408867907)
                      ·
                        rfl

theorem cell23_3295798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_3295798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295798 prefixEnd_3295798 := by exact prefixLift 3295798
  have htrace : WordTrace (prefixWord ++ tailWord_3295798) baseStart_3295798 baseEnd_3295798 := by
    simpa [prefixWord, tailWord_3295798, baseEnd_3295798] using wordTrace_append hprefix tailTrace_3295798
  have hstable : (prefixWord ++ tailWord_3295798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295798).length < 2 ^ (prefixWord ++ tailWord_3295798).sum := by decide
  have hdescent : baseEnd_3295798 < baseStart_3295798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295808 : List Nat := [2, 1, 1, 2, 2, 2, 2, 5, 1, 3, 2]
def baseStart_3295808 : Nat := 118140960795 + 3295808 * 2 ^ 59
def prefixEnd_3295808 : Nat := 4983230072969 + 3 ^ 40 * 3295808 * 2
def baseEnd_3295808 : Nat := 1692333648933546369742861

theorem tailTrace_3295808 : CollatzResearch.WordTrace tailWord_3295808 prefixEnd_3295808 1692333648933546369742861 := by
  unfold tailWord_3295808
  simp only [CollatzResearch.WordTrace]
  refine ⟨60103996621928985019204039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80138662162571980025605385 60103996621928985019204039)
  ·
    refine ⟨90155994932893477528806059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60103996621928985019204039 90155994932893477528806059)
    ·
      refine ⟨135233992399340216293209089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90155994932893477528806059 135233992399340216293209089)
      ·
        refine ⟨101425494299505162219906817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135233992399340216293209089 101425494299505162219906817)
        ·
          refine ⟨76069120724628871664930113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101425494299505162219906817 76069120724628871664930113)
          ·
            refine ⟨57051840543471653748697585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76069120724628871664930113 57051840543471653748697585)
            ·
              refine ⟨42788880407603740311523189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57051840543471653748697585 42788880407603740311523189)
              ·
                refine ⟨4011457538212850654205299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42788880407603740311523189 4011457538212850654205299)
                ·
                  refine ⟨6017186307319275981307949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4011457538212850654205299 6017186307319275981307949)
                  ·
                    refine ⟨2256444865244728492990481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6017186307319275981307949 2256444865244728492990481)
                    ·
                      refine ⟨1692333648933546369742861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2256444865244728492990481 1692333648933546369742861)
                      ·
                        rfl

theorem cell23_3295808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 1, 3, 2].length) (baseStart_3295808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295808 prefixEnd_3295808 := by exact prefixLift 3295808
  have htrace : WordTrace (prefixWord ++ tailWord_3295808) baseStart_3295808 baseEnd_3295808 := by
    simpa [prefixWord, tailWord_3295808, baseEnd_3295808] using wordTrace_append hprefix tailTrace_3295808
  have hstable : (prefixWord ++ tailWord_3295808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295808).length < 2 ^ (prefixWord ++ tailWord_3295808).sum := by decide
  have hdescent : baseEnd_3295808 < baseStart_3295808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295815 : List Nat := [1, 1, 4, 1, 4, 2, 2, 2, 2, 1, 3]
def baseStart_3295815 : Nat := 118140960795 + 3295815 * 2 ^ 59
def prefixEnd_3295815 : Nat := 4983230072969 + 3 ^ 40 * 3295815 * 2
def baseEnd_3295815 : Nat := 1692337243298127842355329

theorem tailTrace_3295815 : CollatzResearch.WordTrace tailWord_3295815 prefixEnd_3295815 1692337243298127842355329 := by
  unfold tailWord_3295815
  simp only [CollatzResearch.WordTrace]
  refine ⟨120208248554832610233912899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80138832369888406822608599 120208248554832610233912899)
  ·
    refine ⟨180312372832248915350869349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120208248554832610233912899 180312372832248915350869349)
    ·
      refine ⟨33808569906046671628288003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180312372832248915350869349 33808569906046671628288003)
      ·
        refine ⟨50712854859070007442432005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33808569906046671628288003 50712854859070007442432005)
        ·
          refine ⟨9508660286075626395456001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50712854859070007442432005 9508660286075626395456001)
          ·
            refine ⟨7131495214556719796592001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9508660286075626395456001 7131495214556719796592001)
            ·
              refine ⟨5348621410917539847444001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7131495214556719796592001 5348621410917539847444001)
              ·
                refine ⟨4011466058188154885583001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5348621410917539847444001 4011466058188154885583001)
                ·
                  refine ⟨3008599543641116164187251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4011466058188154885583001 3008599543641116164187251)
                  ·
                    refine ⟨4512899315461674246280877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3008599543641116164187251 4512899315461674246280877)
                    ·
                      refine ⟨1692337243298127842355329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4512899315461674246280877 1692337243298127842355329)
                      ·
                        rfl

theorem cell23_3295815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_3295815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295815 prefixEnd_3295815 := by exact prefixLift 3295815
  have htrace : WordTrace (prefixWord ++ tailWord_3295815) baseStart_3295815 baseEnd_3295815 := by
    simpa [prefixWord, tailWord_3295815, baseEnd_3295815] using wordTrace_append hprefix tailTrace_3295815
  have hstable : (prefixWord ++ tailWord_3295815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295815).length < 2 ^ (prefixWord ++ tailWord_3295815).sum := by decide
  have hdescent : baseEnd_3295815 < baseStart_3295815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295824 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 5]
def baseStart_3295824 : Nat := 118140960795 + 3295824 * 2 ^ 59
def prefixEnd_3295824 : Nat := 4983230072969 + 3 ^ 40 * 3295824 * 2
def baseEnd_3295824 : Nat := 1692341864624018307142787

theorem tailTrace_3295824 : CollatzResearch.WordTrace tailWord_3295824 prefixEnd_3295824 1692341864624018307142787 := by
  unfold tailWord_3295824
  simp only [CollatzResearch.WordTrace]
  refine ⟨60104288405900002385495263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80139051207866669847327017 60104288405900002385495263)
  ·
    refine ⟨90156432608850003578242895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60104288405900002385495263 90156432608850003578242895)
    ·
      refine ⟨135234648913275005367364343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90156432608850003578242895 135234648913275005367364343)
      ·
        refine ⟨202851973369912508051046515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135234648913275005367364343 202851973369912508051046515)
        ·
          refine ⟨304277960054868762076569773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202851973369912508051046515 304277960054868762076569773)
          ·
            refine ⟨114104235020575785778713665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304277960054868762076569773 114104235020575785778713665)
            ·
              refine ⟨85578176265431839334035249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114104235020575785778713665 85578176265431839334035249)
              ·
                refine ⟨64183632199073879500526437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85578176265431839334035249 64183632199073879500526437)
                ·
                  refine ⟨12034431037326352406348707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64183632199073879500526437 12034431037326352406348707)
                  ·
                    refine ⟨18051646555989528609523061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12034431037326352406348707 18051646555989528609523061)
                    ·
                      refine ⟨1692341864624018307142787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18051646555989528609523061 1692341864624018307142787)
                      ·
                        rfl

theorem cell23_3295824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_3295824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295824 prefixEnd_3295824 := by exact prefixLift 3295824
  have htrace : WordTrace (prefixWord ++ tailWord_3295824) baseStart_3295824 baseEnd_3295824 := by
    simpa [prefixWord, tailWord_3295824, baseEnd_3295824] using wordTrace_append hprefix tailTrace_3295824
  have hstable : (prefixWord ++ tailWord_3295824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295824).length < 2 ^ (prefixWord ++ tailWord_3295824).sum := by decide
  have hdescent : baseEnd_3295824 < baseStart_3295824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295872 : List Nat := [2, 1, 1, 2, 1, 7, 1, 2, 2, 2, 2]
def baseStart_3295872 : Nat := 118140960795 + 3295872 * 2 ^ 59
def prefixEnd_3295872 : Nat := 4983230072969 + 3 ^ 40 * 3295872 * 2
def baseEnd_3295872 : Nat := 1692366511695434119342567

theorem tailTrace_3295872 : CollatzResearch.WordTrace tailWord_3295872 prefixEnd_3295872 1692366511695434119342567 := by
  unfold tailWord_3295872
  simp only [CollatzResearch.WordTrace]
  refine ⟨60105163757813054484368935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80140218343750739312491913 60105163757813054484368935)
  ·
    refine ⟨90157745636719581726553403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60105163757813054484368935 90157745636719581726553403)
    ·
      refine ⟨135236618455079372589830105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90157745636719581726553403 135236618455079372589830105)
      ·
        refine ⟨101427463841309529442372579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135236618455079372589830105 101427463841309529442372579)
        ·
          refine ⟨152141195761964294163558869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101427463841309529442372579 152141195761964294163558869)
          ·
            refine ⟨3565809275671038144458411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 152141195761964294163558869 3565809275671038144458411)
            ·
              refine ⟨5348713913506557216687617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3565809275671038144458411 5348713913506557216687617)
              ·
                refine ⟨4011535435129917912515713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5348713913506557216687617 4011535435129917912515713)
                ·
                  refine ⟨3008651576347438434386785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4011535435129917912515713 3008651576347438434386785)
                  ·
                    refine ⟨2256488682260578825790089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3008651576347438434386785 2256488682260578825790089)
                    ·
                      refine ⟨1692366511695434119342567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2256488682260578825790089 1692366511695434119342567)
                      ·
                        rfl

theorem cell23_3295872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 2, 2, 2].length) (baseStart_3295872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3295872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3295872 prefixEnd_3295872 := by exact prefixLift 3295872
  have htrace : WordTrace (prefixWord ++ tailWord_3295872) baseStart_3295872 baseEnd_3295872 := by
    simpa [prefixWord, tailWord_3295872, baseEnd_3295872] using wordTrace_append hprefix tailTrace_3295872
  have hstable : (prefixWord ++ tailWord_3295872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295872).length < 2 ^ (prefixWord ++ tailWord_3295872).sum := by decide
  have hdescent : baseEnd_3295872 < baseStart_3295872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296028 : List Nat := [2, 2, 3, 1, 1, 3, 2, 2, 1, 6]
def baseStart_3296028 : Nat := 118140960795 + 3296028 * 2 ^ 59
def prefixEnd_3296028 : Nat := 4983230072969 + 3 ^ 40 * 3296028 * 2
def baseEnd_3296028 : Nat := 564148871559178502997283

theorem tailTrace_3296028 : CollatzResearch.WordTrace tailWord_3296028 prefixEnd_3296028 564148871559178502997283 := by
  unfold tailWord_3296028
  simp only [CollatzResearch.WordTrace]
  refine ⟨60108008651530473805708369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80144011535373965074277825 60108008651530473805708369)
  ·
    refine ⟨45081006488647855354281277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60108008651530473805708369 45081006488647855354281277)
    ·
      refine ⟨16905377433242945757855479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45081006488647855354281277 16905377433242945757855479)
      ·
        refine ⟨25358066149864418636783219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16905377433242945757855479 25358066149864418636783219)
        ·
          refine ⟨38037099224796627955174829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25358066149864418636783219 38037099224796627955174829)
          ·
            refine ⟨14263912209298735483190561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38037099224796627955174829 14263912209298735483190561)
            ·
              refine ⟨10697934156974051612392921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14263912209298735483190561 10697934156974051612392921)
              ·
                refine ⟨8023450617730538709294691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10697934156974051612392921 8023450617730538709294691)
                ·
                  refine ⟨12035175926595808063942037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8023450617730538709294691 12035175926595808063942037)
                  ·
                    refine ⟨564148871559178502997283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12035175926595808063942037 564148871559178502997283)
                    ·
                      rfl

theorem cell23_3296028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_3296028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296028 prefixEnd_3296028 := by exact prefixLift 3296028
  have htrace : WordTrace (prefixWord ++ tailWord_3296028) baseStart_3296028 baseEnd_3296028 := by
    simpa [prefixWord, tailWord_3296028, baseEnd_3296028] using wordTrace_append hprefix tailTrace_3296028
  have hstable : (prefixWord ++ tailWord_3296028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296028).length < 2 ^ (prefixWord ++ tailWord_3296028).sum := by decide
  have hdescent : baseEnd_3296028 < baseStart_3296028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296032 : List Nat := [2, 1, 1, 5, 1, 4, 2, 1, 1, 5]
def baseStart_3296032 : Nat := 118140960795 + 3296032 * 2 ^ 59
def prefixEnd_3296032 : Nat := 4983230072969 + 3 ^ 40 * 3296032 * 2
def baseEnd_3296032 : Nat := 564149556200051164447277

theorem tailTrace_3296032 : CollatzResearch.WordTrace tailWord_3296032 prefixEnd_3296032 564149556200051164447277 := by
  unfold tailWord_3296032
  simp only [CollatzResearch.WordTrace]
  refine ⟨60108081597523228147281175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80144108796697637529708233 60108081597523228147281175)
  ·
    refine ⟨90162122396284842220921763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60108081597523228147281175 90162122396284842220921763)
    ·
      refine ⟨135243183594427263331382645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90162122396284842220921763 135243183594427263331382645)
      ·
        refine ⟨12679048461977555937317123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135243183594427263331382645 12679048461977555937317123)
        ·
          refine ⟨19018572692966333905975685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12679048461977555937317123 19018572692966333905975685)
          ·
            refine ⟨3565982379931187607370441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19018572692966333905975685 3565982379931187607370441)
            ·
              refine ⟨2674486784948390705527831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3565982379931187607370441 2674486784948390705527831)
              ·
                refine ⟨4011730177422586058291747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2674486784948390705527831 4011730177422586058291747)
                ·
                  refine ⟨6017595266133879087437621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4011730177422586058291747 6017595266133879087437621)
                  ·
                    refine ⟨564149556200051164447277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6017595266133879087437621 564149556200051164447277)
                    ·
                      rfl

theorem cell23_3296032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 1, 5].length) (baseStart_3296032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296032 prefixEnd_3296032 := by exact prefixLift 3296032
  have htrace : WordTrace (prefixWord ++ tailWord_3296032) baseStart_3296032 baseEnd_3296032 := by
    simpa [prefixWord, tailWord_3296032, baseEnd_3296032] using wordTrace_append hprefix tailTrace_3296032
  have hstable : (prefixWord ++ tailWord_3296032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296032).length < 2 ^ (prefixWord ++ tailWord_3296032).sum := by decide
  have hdescent : baseEnd_3296032 < baseStart_3296032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296035 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 7, 2, 2]
def baseStart_3296035 : Nat := 118140960795 + 3296035 * 2 ^ 59
def prefixEnd_3296035 : Nat := 4983230072969 + 3 ^ 40 * 3296035 * 2
def baseEnd_3296035 : Nat := 1692450209042116981604317

theorem tailTrace_3296035 : CollatzResearch.WordTrace tailWord_3296035 prefixEnd_3296035 1692450209042116981604317 := by
  unfold tailWord_3296035
  simp only [CollatzResearch.WordTrace]
  refine ⟨120216272614035587806921559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80144181742690391871281039 120216272614035587806921559)
  ·
    refine ⟨180324408921053381710382339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120216272614035587806921559 180324408921053381710382339)
    ·
      refine ⟨270486613381580072565573509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180324408921053381710382339 270486613381580072565573509)
      ·
        refine ⟨50716240009046263606045033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270486613381580072565573509 50716240009046263606045033)
        ·
          refine ⟨38037180006784697704533775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50716240009046263606045033 38037180006784697704533775)
          ·
            refine ⟨57055770010177046556800663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38037180006784697704533775 57055770010177046556800663)
            ·
              refine ⟨85583655015265569835200995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57055770010177046556800663 85583655015265569835200995)
              ·
                refine ⟨128375482522898354752801493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85583655015265569835200995 128375482522898354752801493)
                ·
                  refine ⟨3008800371630430189518785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 128375482522898354752801493 3008800371630430189518785)
                  ·
                    refine ⟨2256600278722822642139089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3008800371630430189518785 2256600278722822642139089)
                    ·
                      refine ⟨1692450209042116981604317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2256600278722822642139089 1692450209042116981604317)
                      ·
                        rfl

theorem cell23_3296035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_3296035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296035 prefixEnd_3296035 := by exact prefixLift 3296035
  have htrace : WordTrace (prefixWord ++ tailWord_3296035) baseStart_3296035 baseEnd_3296035 := by
    simpa [prefixWord, tailWord_3296035, baseEnd_3296035] using wordTrace_append hprefix tailTrace_3296035
  have hstable : (prefixWord ++ tailWord_3296035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296035).length < 2 ^ (prefixWord ++ tailWord_3296035).sum := by decide
  have hdescent : baseEnd_3296035 < baseStart_3296035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296062 : List Nat := [4, 2, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_3296062 : Nat := 118140960795 + 3296062 * 2 ^ 59
def prefixEnd_3296062 : Nat := 4983230072969 + 3 ^ 40 * 3296062 * 2
def baseEnd_3296062 : Nat := 564154691006596125322231

theorem tailTrace_3296062 : CollatzResearch.WordTrace tailWord_3296062 prefixEnd_3296062 564154691006596125322231 := by
  unfold tailWord_3296062
  simp only [CollatzResearch.WordTrace]
  refine ⟨15027157173117221427269305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80144838256625180945436293 15027157173117221427269305)
  ·
    refine ⟨11270367879837916070451979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15027157173117221427269305 11270367879837916070451979)
    ·
      refine ⟨16905551819756874105677969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11270367879837916070451979 16905551819756874105677969)
      ·
        refine ⟨12679163864817655579258477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16905551819756874105677969 12679163864817655579258477)
        ·
          refine ⟨4754686449306620842221929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12679163864817655579258477 4754686449306620842221929)
          ·
            refine ⟨3566014836979965631666447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4754686449306620842221929 3566014836979965631666447)
            ·
              refine ⟨5349022255469948447499671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3566014836979965631666447 5349022255469948447499671)
              ·
                refine ⟨8023533383204922671249507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5349022255469948447499671 8023533383204922671249507)
                ·
                  refine ⟨12035300074807384006874261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8023533383204922671249507 12035300074807384006874261)
                  ·
                    refine ⟨564154691006596125322231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12035300074807384006874261 564154691006596125322231)
                    ·
                      rfl

theorem cell23_3296062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_3296062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296062 prefixEnd_3296062 := by exact prefixLift 3296062
  have htrace : WordTrace (prefixWord ++ tailWord_3296062) baseStart_3296062 baseEnd_3296062 := by
    simpa [prefixWord, tailWord_3296062, baseEnd_3296062] using wordTrace_append hprefix tailTrace_3296062
  have hstable : (prefixWord ++ tailWord_3296062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296062).length < 2 ^ (prefixWord ++ tailWord_3296062).sum := by decide
  have hdescent : baseEnd_3296062 < baseStart_3296062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296085 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 6, 1, 3]
def baseStart_3296085 : Nat := 118140960795 + 3296085 * 2 ^ 59
def prefixEnd_3296085 : Nat := 4983230072969 + 3 ^ 40 * 3296085 * 2
def baseEnd_3296085 : Nat := 1692475883074841785979087

theorem tailTrace_3296085 : CollatzResearch.WordTrace tailWord_3296085 prefixEnd_3296085 1692475883074841785979087 := by
  unfold tailWord_3296085
  simp only [CollatzResearch.WordTrace]
  refine ⟨120218096263854446346241709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80145397509236297564161139 120218096263854446346241709)
  ·
    refine ⟨45081786098945417379840641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120218096263854446346241709 45081786098945417379840641)
    ·
      refine ⟨33811339574209063034880481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45081786098945417379840641 33811339574209063034880481)
      ·
        refine ⟨25358504680656797276160361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33811339574209063034880481 25358504680656797276160361)
        ·
          refine ⟨19018878510492597957120271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25358504680656797276160361 19018878510492597957120271)
          ·
            refine ⟨28528317765738896935680407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19018878510492597957120271 28528317765738896935680407)
            ·
              refine ⟨42792476648608345403520611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28528317765738896935680407 42792476648608345403520611)
              ·
                refine ⟨64188714972912518105280917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42792476648608345403520611 64188714972912518105280917)
                ·
                  refine ⟨3008846014355274286185043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64188714972912518105280917 3008846014355274286185043)
                  ·
                    refine ⟨4513269021532911429277565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3008846014355274286185043 4513269021532911429277565)
                    ·
                      refine ⟨1692475883074841785979087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4513269021532911429277565 1692475883074841785979087)
                      ·
                        rfl

theorem cell23_3296085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_3296085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296085 prefixEnd_3296085 := by exact prefixLift 3296085
  have htrace : WordTrace (prefixWord ++ tailWord_3296085) baseStart_3296085 baseEnd_3296085 := by
    simpa [prefixWord, tailWord_3296085, baseEnd_3296085] using wordTrace_append hprefix tailTrace_3296085
  have hstable : (prefixWord ++ tailWord_3296085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296085).length < 2 ^ (prefixWord ++ tailWord_3296085).sum := by decide
  have hdescent : baseEnd_3296085 < baseStart_3296085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296108 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 4]
def baseStart_3296108 : Nat := 118140960795 + 3296108 * 2 ^ 59
def prefixEnd_3296108 : Nat := 4983230072969 + 3 ^ 40 * 3296108 * 2
def baseEnd_3296108 : Nat := 1692487693129895195991481

theorem tailTrace_3296108 : CollatzResearch.WordTrace tailWord_3296108 prefixEnd_3296108 1692487693129895195991481 := by
  unfold tailWord_3296108
  simp only [CollatzResearch.WordTrace]
  refine ⟨60109467571385560637164489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80145956761847414182885985 60109467571385560637164489)
  ·
    refine ⟨45082100678539170477873367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60109467571385560637164489 45082100678539170477873367)
    ·
      refine ⟨67623151017808755716810051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45082100678539170477873367 67623151017808755716810051)
      ·
        refine ⟨101434726526713133575215077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67623151017808755716810051 101434726526713133575215077)
        ·
          refine ⟨19019011223758712545352827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101434726526713133575215077 19019011223758712545352827)
          ·
            refine ⟨28528516835638068818029241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19019011223758712545352827 28528516835638068818029241)
            ·
              refine ⟨21396387626728551613521931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28528516835638068818029241 21396387626728551613521931)
              ·
                refine ⟨32094581440092827420282897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21396387626728551613521931 32094581440092827420282897)
                ·
                  refine ⟨24070936080069620565212173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32094581440092827420282897 24070936080069620565212173)
                  ·
                    refine ⟨9026601030026107711954565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24070936080069620565212173 9026601030026107711954565)
                    ·
                      refine ⟨1692487693129895195991481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9026601030026107711954565 1692487693129895195991481)
                      ·
                        rfl

theorem cell23_3296108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_3296108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296108 prefixEnd_3296108 := by exact prefixLift 3296108
  have htrace : WordTrace (prefixWord ++ tailWord_3296108) baseStart_3296108 baseEnd_3296108 := by
    simpa [prefixWord, tailWord_3296108, baseEnd_3296108] using wordTrace_append hprefix tailTrace_3296108
  have hstable : (prefixWord ++ tailWord_3296108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296108).length < 2 ^ (prefixWord ++ tailWord_3296108).sum := by decide
  have hdescent : baseEnd_3296108 < baseStart_3296108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296128 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 3]
def baseStart_3296128 : Nat := 118140960795 + 3296128 * 2 ^ 59
def prefixEnd_3296128 : Nat := 4983230072969 + 3 ^ 40 * 3296128 * 2
def baseEnd_3296128 : Nat := 1692497962742985117741389

theorem tailTrace_3296128 : CollatzResearch.WordTrace tailWord_3296128 prefixEnd_3296128 1692497962742985117741389 := by
  unfold tailWord_3296128
  simp only [CollatzResearch.WordTrace]
  refine ⟨60109832301349332345028519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80146443068465776460038025 60109832301349332345028519)
  ·
    refine ⟨90164748452023998517542779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60109832301349332345028519 90164748452023998517542779)
    ·
      refine ⟨135247122678035997776314169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90164748452023998517542779 135247122678035997776314169)
      ·
        refine ⟨101435342008526998332235627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135247122678035997776314169 101435342008526998332235627)
        ·
          refine ⟨152153013012790497498353441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101435342008526998332235627 152153013012790497498353441)
          ·
            refine ⟨114114759759592873123765081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152153013012790497498353441 114114759759592873123765081)
            ·
              refine ⟨85586069819694654842823811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114114759759592873123765081 85586069819694654842823811)
              ·
                refine ⟨128379104729541982264235717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85586069819694654842823811 128379104729541982264235717)
                ·
                  refine ⟨24071082136789121674544197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128379104729541982264235717 24071082136789121674544197)
                  ·
                    refine ⟨4513327900647960313977037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24071082136789121674544197 4513327900647960313977037)
                    ·
                      refine ⟨1692497962742985117741389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4513327900647960313977037 1692497962742985117741389)
                      ·
                        rfl

theorem cell23_3296128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_3296128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296128 prefixEnd_3296128 := by exact prefixLift 3296128
  have htrace : WordTrace (prefixWord ++ tailWord_3296128) baseStart_3296128 baseEnd_3296128 := by
    simpa [prefixWord, tailWord_3296128, baseEnd_3296128] using wordTrace_append hprefix tailTrace_3296128
  have hstable : (prefixWord ++ tailWord_3296128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296128).length < 2 ^ (prefixWord ++ tailWord_3296128).sum := by decide
  have hdescent : baseEnd_3296128 < baseStart_3296128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296159 : List Nat := [1, 1, 2, 5, 2, 1, 1, 4, 2, 2, 2]
def baseStart_3296159 : Nat := 118140960795 + 3296159 * 2 ^ 59
def prefixEnd_3296159 : Nat := 4983230072969 + 3 ^ 40 * 3296159 * 2
def baseEnd_3296159 : Nat := 1692513880643274496453747

theorem tailTrace_3296159 : CollatzResearch.WordTrace tailWord_3296159 prefixEnd_3296159 1692513880643274496453747 := by
  unfold tailWord_3296159
  simp only [CollatzResearch.WordTrace]
  refine ⟨120220795265586356984435531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80147196843724237989623687 120220795265586356984435531)
  ·
    refine ⟨180331192898379535476653297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120220795265586356984435531 180331192898379535476653297)
    ·
      refine ⟨135248394673784651607489973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180331192898379535476653297 135248394673784651607489973)
      ·
        refine ⟨12679537000667311088202185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135248394673784651607489973 12679537000667311088202185)
        ·
          refine ⟨9509652750500483316151639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12679537000667311088202185 9509652750500483316151639)
          ·
            refine ⟨14264479125750724974227459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9509652750500483316151639 14264479125750724974227459)
            ·
              refine ⟨21396718688626087461341189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14264479125750724974227459 21396718688626087461341189)
              ·
                refine ⟨4011884754117391399001473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21396718688626087461341189 4011884754117391399001473)
                ·
                  refine ⟨3008913565588043549251105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4011884754117391399001473 3008913565588043549251105)
                  ·
                    refine ⟨2256685174191032661938329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3008913565588043549251105 2256685174191032661938329)
                    ·
                      refine ⟨1692513880643274496453747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2256685174191032661938329 1692513880643274496453747)
                      ·
                        rfl

theorem cell23_3296159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_3296159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296159 prefixEnd_3296159 := by exact prefixLift 3296159
  have htrace : WordTrace (prefixWord ++ tailWord_3296159) baseStart_3296159 baseEnd_3296159 := by
    simpa [prefixWord, tailWord_3296159, baseEnd_3296159] using wordTrace_append hprefix tailTrace_3296159
  have hstable : (prefixWord ++ tailWord_3296159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296159).length < 2 ^ (prefixWord ++ tailWord_3296159).sum := by decide
  have hdescent : baseEnd_3296159 < baseStart_3296159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296232 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 2, 4, 2]
def baseStart_3296232 : Nat := 118140960795 + 3296232 * 2 ^ 59
def prefixEnd_3296232 : Nat := 4983230072969 + 3 ^ 40 * 3296232 * 2
def baseEnd_3296232 : Nat := 1692551364731052710840911

theorem tailTrace_3296232 : CollatzResearch.WordTrace tailWord_3296232 prefixEnd_3296232 1692551364731052710840911 := by
  unfold tailWord_3296232
  simp only [CollatzResearch.WordTrace]
  refine ⟨60111728897160945225921475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80148971862881260301228633 60111728897160945225921475)
  ·
    refine ⟨90167593345741417838882213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60111728897160945225921475 90167593345741417838882213)
    ·
      refine ⟨16906423752326515844790415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90167593345741417838882213 16906423752326515844790415)
      ·
        refine ⟨25359635628489773767185623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16906423752326515844790415 25359635628489773767185623)
        ·
          refine ⟨38039453442734660650778435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25359635628489773767185623 38039453442734660650778435)
          ·
            refine ⟨57059180164101990976167653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38039453442734660650778435 57059180164101990976167653)
            ·
              refine ⟨10698596280769123308031435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57059180164101990976167653 10698596280769123308031435)
              ·
                refine ⟨16047894421153684962047153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10698596280769123308031435 16047894421153684962047153)
                ·
                  refine ⟨12035920815865263721535365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16047894421153684962047153 12035920815865263721535365)
                  ·
                    refine ⟨2256735152974736947787881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12035920815865263721535365 2256735152974736947787881)
                    ·
                      refine ⟨1692551364731052710840911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2256735152974736947787881 1692551364731052710840911)
                      ·
                        rfl

theorem cell23_3296232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_3296232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296232 prefixEnd_3296232 := by exact prefixLift 3296232
  have htrace : WordTrace (prefixWord ++ tailWord_3296232) baseStart_3296232 baseEnd_3296232 := by
    simpa [prefixWord, tailWord_3296232, baseEnd_3296232] using wordTrace_append hprefix tailTrace_3296232
  have hstable : (prefixWord ++ tailWord_3296232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296232).length < 2 ^ (prefixWord ++ tailWord_3296232).sum := by decide
  have hdescent : baseEnd_3296232 < baseStart_3296232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296289 : List Nat := [1, 2, 3, 2, 3, 3, 2, 1, 6]
def baseStart_3296289 : Nat := 118140960795 + 3296289 * 2 ^ 59
def prefixEnd_3296289 : Nat := 4983230072969 + 3 ^ 40 * 3296289 * 2
def baseEnd_3296289 : Nat := 188064514792039887536461

theorem tailTrace_3296289 : CollatzResearch.WordTrace tailWord_3296289 prefixEnd_3296289 188064514792039887536461 := by
  unfold tailWord_3296289
  simp only [CollatzResearch.WordTrace]
  refine ⟨120225536755115389186667921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80150357836743592791111947 120225536755115389186667921)
  ·
    refine ⟨90169152566336541890000941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120225536755115389186667921 90169152566336541890000941)
    ·
      refine ⟨33813432212376203208750353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90169152566336541890000941 33813432212376203208750353)
      ·
        refine ⟨25360074159282152406562765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33813432212376203208750353 25360074159282152406562765)
        ·
          refine ⟨9510027809730807152461037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25360074159282152406562765 9510027809730807152461037)
          ·
            refine ⟨3566260428649052682172889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9510027809730807152461037 3566260428649052682172889)
            ·
              refine ⟨2674695321486789511629667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3566260428649052682172889 2674695321486789511629667)
              ·
                refine ⟨4012042982230184267444501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2674695321486789511629667 4012042982230184267444501)
                ·
                  refine ⟨188064514792039887536461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4012042982230184267444501 188064514792039887536461)
                  ·
                    rfl

theorem cell23_3296289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 6].length) (baseStart_3296289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296289 prefixEnd_3296289 := by exact prefixLift 3296289
  have htrace : WordTrace (prefixWord ++ tailWord_3296289) baseStart_3296289 baseEnd_3296289 := by
    simpa [prefixWord, tailWord_3296289, baseEnd_3296289] using wordTrace_append hprefix tailTrace_3296289
  have hstable : (prefixWord ++ tailWord_3296289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296289).length < 2 ^ (prefixWord ++ tailWord_3296289).sum := by decide
  have hdescent : baseEnd_3296289 < baseStart_3296289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296302 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 3, 5]
def baseStart_3296302 : Nat := 118140960795 + 3296302 * 2 ^ 59
def prefixEnd_3296302 : Nat := 4983230072969 + 3 ^ 40 * 3296302 * 2
def baseEnd_3296302 : Nat := 564195769458955812321863

theorem tailTrace_3296302 : CollatzResearch.WordTrace tailWord_3296302 prefixEnd_3296302 564195769458955812321863 := by
  unfold tailWord_3296302
  simp only [CollatzResearch.WordTrace]
  refine ⟨15028251363008536550861395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80150673936045528271260773 15028251363008536550861395)
  ·
    refine ⟨22542377044512804826292093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15028251363008536550861395 22542377044512804826292093)
    ·
      refine ⟨8453391391692301809859535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22542377044512804826292093 8453391391692301809859535)
      ·
        refine ⟨12680087087538452714789303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8453391391692301809859535 12680087087538452714789303)
        ·
          refine ⟨19020130631307679072183955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12680087087538452714789303 19020130631307679072183955)
          ·
            refine ⟨28530195946961518608275933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19020130631307679072183955 28530195946961518608275933)
            ·
              refine ⟨10698823480110569478103475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28530195946961518608275933 10698823480110569478103475)
              ·
                refine ⟨16048235220165854217155213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10698823480110569478103475 16048235220165854217155213)
                ·
                  refine ⟨6018088207562195331433205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16048235220165854217155213 6018088207562195331433205)
                  ·
                    refine ⟨564195769458955812321863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6018088207562195331433205 564195769458955812321863)
                    ·
                      rfl

theorem cell23_3296302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_3296302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296302 prefixEnd_3296302 := by exact prefixLift 3296302
  have htrace : WordTrace (prefixWord ++ tailWord_3296302) baseStart_3296302 baseEnd_3296302 := by
    simpa [prefixWord, tailWord_3296302, baseEnd_3296302] using wordTrace_append hprefix tailTrace_3296302
  have hstable : (prefixWord ++ tailWord_3296302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296302).length < 2 ^ (prefixWord ++ tailWord_3296302).sum := by decide
  have hdescent : baseEnd_3296302 < baseStart_3296302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296333 : List Nat := [1, 6, 1, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_3296333 : Nat := 118140960795 + 3296333 * 2 ^ 59
def prefixEnd_3296333 : Nat := 4983230072969 + 3 ^ 40 * 3296333 * 2
def baseEnd_3296333 : Nat := 1692603226277156815677947

theorem tailTrace_3296333 : CollatzResearch.WordTrace tailWord_3296333 prefixEnd_3296333 1692603226277156815677947 := by
  unfold tailWord_3296333
  simp only [CollatzResearch.WordTrace]
  refine ⟨120227141566955984701269653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80151427711303989800846435 120227141566955984701269653)
  ·
    refine ⟨5635647260951061782872015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120227141566955984701269653 5635647260951061782872015)
    ·
      refine ⟨8453470891426592674308023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5635647260951061782872015 8453470891426592674308023)
      ·
        refine ⟨12680206337139889011462035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8453470891426592674308023 12680206337139889011462035)
        ·
          refine ⟨19020309505709833517193053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12680206337139889011462035 19020309505709833517193053)
          ·
            refine ⟨7132616064641187568947395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19020309505709833517193053 7132616064641187568947395)
            ·
              refine ⟨10698924096961781353421093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7132616064641187568947395 10698924096961781353421093)
              ·
                refine ⟨2006048268180334003766455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10698924096961781353421093 2006048268180334003766455)
                ·
                  refine ⟨3009072402270501005649683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2006048268180334003766455 3009072402270501005649683)
                  ·
                    refine ⟨4513608603405751508474525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3009072402270501005649683 4513608603405751508474525)
                    ·
                      refine ⟨1692603226277156815677947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4513608603405751508474525 1692603226277156815677947)
                      ·
                        rfl

theorem cell23_3296333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_3296333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296333 prefixEnd_3296333 := by exact prefixLift 3296333
  have htrace : WordTrace (prefixWord ++ tailWord_3296333) baseStart_3296333 baseEnd_3296333 := by
    simpa [prefixWord, tailWord_3296333, baseEnd_3296333] using wordTrace_append hprefix tailTrace_3296333
  have hstable : (prefixWord ++ tailWord_3296333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296333).length < 2 ^ (prefixWord ++ tailWord_3296333).sum := by decide
  have hdescent : baseEnd_3296333 < baseStart_3296333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296352 : List Nat := [2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 4]
def baseStart_3296352 : Nat := 118140960795 + 3296352 * 2 ^ 59
def prefixEnd_3296352 : Nat := 4983230072969 + 3 ^ 40 * 3296352 * 2
def baseEnd_3296352 : Nat := 1692612982409592241340359

theorem tailTrace_3296352 : CollatzResearch.WordTrace tailWord_3296352 prefixEnd_3296352 1692612982409592241340359 := by
  unfold tailWord_3296352
  simp only [CollatzResearch.WordTrace]
  refine ⟨60113917276943575473105655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80151889702591433964140873 60113917276943575473105655)
  ·
    refine ⟨90170875915415363209658483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60113917276943575473105655 90170875915415363209658483)
    ·
      refine ⟨135256313873123044814487725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90170875915415363209658483 135256313873123044814487725)
      ·
        refine ⟨50721117702421141805432897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135256313873123044814487725 50721117702421141805432897)
        ·
          refine ⟨38040838276815856354074673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50721117702421141805432897 38040838276815856354074673)
          ·
            refine ⟨28530628707611892265556005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38040838276815856354074673 28530628707611892265556005)
            ·
              refine ⟨5349492882677229799791751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28530628707611892265556005 5349492882677229799791751)
              ·
                refine ⟨8024239324015844699687627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5349492882677229799791751 8024239324015844699687627)
                ·
                  refine ⟨12036358986023767049531441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8024239324015844699687627 12036358986023767049531441)
                  ·
                    refine ⟨9027269239517825287148581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12036358986023767049531441 9027269239517825287148581)
                    ·
                      refine ⟨1692612982409592241340359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9027269239517825287148581 1692612982409592241340359)
                      ·
                        rfl

theorem cell23_3296352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_3296352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296352 prefixEnd_3296352 := by exact prefixLift 3296352
  have htrace : WordTrace (prefixWord ++ tailWord_3296352) baseStart_3296352 baseEnd_3296352 := by
    simpa [prefixWord, tailWord_3296352, baseEnd_3296352] using wordTrace_append hprefix tailTrace_3296352
  have hstable : (prefixWord ++ tailWord_3296352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296352).length < 2 ^ (prefixWord ++ tailWord_3296352).sum := by decide
  have hdescent : baseEnd_3296352 < baseStart_3296352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296360 : List Nat := [2, 1, 4, 4, 2, 1, 1, 1, 2, 3, 2]
def baseStart_3296360 : Nat := 118140960795 + 3296360 * 2 ^ 59
def prefixEnd_3296360 : Nat := 4983230072969 + 3 ^ 40 * 3296360 * 2
def baseEnd_3296360 : Nat := 1692617090254828210040323

theorem tailTrace_3296360 : CollatzResearch.WordTrace tailWord_3296360 prefixEnd_3296360 1692617090254828210040323 := by
  unfold tailWord_3296360
  simp only [CollatzResearch.WordTrace]
  refine ⟨60114063168929084156251267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80152084225238778875001689 60114063168929084156251267)
  ·
    refine ⟨90171094753393626234376901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60114063168929084156251267 90171094753393626234376901)
    ·
      refine ⟨16907080266261304918945669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90171094753393626234376901 16907080266261304918945669)
      ·
        refine ⟨3170077549923994672302313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16907080266261304918945669 3170077549923994672302313)
        ·
          refine ⟨2377558162442996004226735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3170077549923994672302313 2377558162442996004226735)
          ·
            refine ⟨3566337243664494006340103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2377558162442996004226735 3566337243664494006340103)
            ·
              refine ⟨5349505865496741009510155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3566337243664494006340103 5349505865496741009510155)
              ·
                refine ⟨8024258798245111514265233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5349505865496741009510155 8024258798245111514265233)
                ·
                  refine ⟨6018194098683833635698925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8024258798245111514265233 6018194098683833635698925)
                  ·
                    refine ⟨2256822787006437613387097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6018194098683833635698925 2256822787006437613387097)
                    ·
                      refine ⟨1692617090254828210040323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2256822787006437613387097 1692617090254828210040323)
                      ·
                        rfl

theorem cell23_3296360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_3296360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296360 prefixEnd_3296360 := by exact prefixLift 3296360
  have htrace : WordTrace (prefixWord ++ tailWord_3296360) baseStart_3296360 baseEnd_3296360 := by
    simpa [prefixWord, tailWord_3296360, baseEnd_3296360] using wordTrace_append hprefix tailTrace_3296360
  have hstable : (prefixWord ++ tailWord_3296360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296360).length < 2 ^ (prefixWord ++ tailWord_3296360).sum := by decide
  have hdescent : baseEnd_3296360 < baseStart_3296360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296395 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 4]
def baseStart_3296395 : Nat := 118140960795 + 3296395 * 2 ^ 59
def prefixEnd_3296395 : Nat := 4983230072969 + 3 ^ 40 * 3296395 * 2
def baseEnd_3296395 : Nat := 1692635062077735573102661

theorem tailTrace_3296395 : CollatzResearch.WordTrace tailWord_3296395 prefixEnd_3296395 1692635062077735573102661 := by
  unfold tailWord_3296395
  simp only [CollatzResearch.WordTrace]
  refine ⟨120229402892731369290026639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80152935261820912860017759 120229402892731369290026639)
  ·
    refine ⟨180344104339097053935039959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120229402892731369290026639 180344104339097053935039959)
    ·
      refine ⟨270516156508645580902559939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180344104339097053935039959 270516156508645580902559939)
      ·
        refine ⟨405774234762968371353839909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270516156508645580902559939 405774234762968371353839909)
        ·
          refine ⟨76082669018056569628844983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 405774234762968371353839909 76082669018056569628844983)
          ·
            refine ⟨114124003527084854443267475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76082669018056569628844983 114124003527084854443267475)
            ·
              refine ⟨171186005290627281664901213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114124003527084854443267475 171186005290627281664901213)
              ·
                refine ⟨64194751983985230624337955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171186005290627281664901213 64194751983985230624337955)
                ·
                  refine ⟨96292127975977845936506933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64194751983985230624337955 96292127975977845936506933)
                  ·
                    refine ⟨9027386997747923056547525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96292127975977845936506933 9027386997747923056547525)
                    ·
                      refine ⟨1692635062077735573102661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9027386997747923056547525 1692635062077735573102661)
                      ·
                        rfl

theorem cell23_3296395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 4].length) (baseStart_3296395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296395 prefixEnd_3296395 := by exact prefixLift 3296395
  have htrace : WordTrace (prefixWord ++ tailWord_3296395) baseStart_3296395 baseEnd_3296395 := by
    simpa [prefixWord, tailWord_3296395, baseEnd_3296395] using wordTrace_append hprefix tailTrace_3296395
  have hstable : (prefixWord ++ tailWord_3296395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296395).length < 2 ^ (prefixWord ++ tailWord_3296395).sum := by decide
  have hdescent : baseEnd_3296395 < baseStart_3296395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296405 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 1, 8]
def baseStart_3296405 : Nat := 118140960795 + 3296405 * 2 ^ 59
def prefixEnd_3296405 : Nat := 4983230072969 + 3 ^ 40 * 3296405 * 2
def baseEnd_3296405 : Nat := 564213398961426844659205

theorem tailTrace_3296405 : CollatzResearch.WordTrace tailWord_3296405 prefixEnd_3296405 564213398961426844659205 := by
  unfold tailWord_3296405
  simp only [CollatzResearch.WordTrace]
  refine ⟨120229767622695140997890669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80153178415130093998593779 120229767622695140997890669)
  ·
    refine ⟨45086162858510677874209001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120229767622695140997890669 45086162858510677874209001)
    ·
      refine ⟨33814622143883008405656751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45086162858510677874209001 33814622143883008405656751)
      ·
        refine ⟨50721933215824512608485127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33814622143883008405656751 50721933215824512608485127)
        ·
          refine ⟨76082899823736768912727691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50721933215824512608485127 76082899823736768912727691)
          ·
            refine ⟨114124349735605153369091537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76082899823736768912727691 114124349735605153369091537)
            ·
              refine ⟨85593262301703865026818653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114124349735605153369091537 85593262301703865026818653)
              ·
                refine ⟨32097473363138949385056995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85593262301703865026818653 32097473363138949385056995)
                ·
                  refine ⟨48146210044708424077585493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32097473363138949385056995 48146210044708424077585493)
                  ·
                    refine ⟨564213398961426844659205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48146210044708424077585493 564213398961426844659205)
                    ·
                      rfl

theorem cell23_3296405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_3296405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296405 prefixEnd_3296405 := by exact prefixLift 3296405
  have htrace : WordTrace (prefixWord ++ tailWord_3296405) baseStart_3296405 baseEnd_3296405 := by
    simpa [prefixWord, tailWord_3296405, baseEnd_3296405] using wordTrace_append hprefix tailTrace_3296405
  have hstable : (prefixWord ++ tailWord_3296405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296405).length < 2 ^ (prefixWord ++ tailWord_3296405).sum := by decide
  have hdescent : baseEnd_3296405 < baseStart_3296405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296416 : List Nat := [2, 1, 1, 4, 2, 1, 4, 2, 1, 3, 2]
def baseStart_3296416 : Nat := 118140960795 + 3296416 * 2 ^ 59
def prefixEnd_3296416 : Nat := 4983230072969 + 3 ^ 40 * 3296416 * 2
def baseEnd_3296416 : Nat := 1692645845171479990940065

theorem tailTrace_3296416 : CollatzResearch.WordTrace tailWord_3296416 prefixEnd_3296416 1692645845171479990940065 := by
  unfold tailWord_3296416
  simp only [CollatzResearch.WordTrace]
  refine ⟨60115084412827644938270551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80153445883770193251027401 60115084412827644938270551)
  ·
    refine ⟨90172626619241467407405827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60115084412827644938270551 90172626619241467407405827)
    ·
      refine ⟨135258939928862201111108741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90172626619241467407405827 135258939928862201111108741)
      ·
        refine ⟨25361051236661662708332889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135258939928862201111108741 25361051236661662708332889)
        ·
          refine ⟨19020788427496247031249667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25361051236661662708332889 19020788427496247031249667)
          ·
            refine ⟨28531182641244370546874501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19020788427496247031249667 28531182641244370546874501)
            ·
              refine ⟨5349596745233319477538969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28531182641244370546874501 5349596745233319477538969)
              ·
                refine ⟨4012197558924989608154227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5349596745233319477538969 4012197558924989608154227)
                ·
                  refine ⟨6018296338387484412231341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4012197558924989608154227 6018296338387484412231341)
                  ·
                    refine ⟨2256861126895306654586753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6018296338387484412231341 2256861126895306654586753)
                    ·
                      refine ⟨1692645845171479990940065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2256861126895306654586753 1692645845171479990940065)
                      ·
                        rfl

theorem cell23_3296416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_3296416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296416 prefixEnd_3296416 := by exact prefixLift 3296416
  have htrace : WordTrace (prefixWord ++ tailWord_3296416) baseStart_3296416 baseEnd_3296416 := by
    simpa [prefixWord, tailWord_3296416, baseEnd_3296416] using wordTrace_append hprefix tailTrace_3296416
  have hstable : (prefixWord ++ tailWord_3296416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296416).length < 2 ^ (prefixWord ++ tailWord_3296416).sum := by decide
  have hdescent : baseEnd_3296416 < baseStart_3296416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296435 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 9]
def baseStart_3296435 : Nat := 118140960795 + 3296435 * 2 ^ 59
def prefixEnd_3296435 : Nat := 4983230072969 + 3 ^ 40 * 3296435 * 2
def baseEnd_3296435 : Nat := 188072844589323935178053

theorem tailTrace_3296435 : CollatzResearch.WordTrace tailWord_3296435 prefixEnd_3296435 188072844589323935178053 := by
  unfold tailWord_3296435
  simp only [CollatzResearch.WordTrace]
  refine ⟨120230861812586456121482759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80153907875057637414321839 120230861812586456121482759)
  ·
    refine ⟨180346292718879684182224139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120230861812586456121482759 180346292718879684182224139)
    ·
      refine ⟨270519439078319526273336209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180346292718879684182224139 270519439078319526273336209)
      ·
        refine ⟨202889579308739644705002157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270519439078319526273336209 202889579308739644705002157)
        ·
          refine ⟨76083592240777366764375809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202889579308739644705002157 76083592240777366764375809)
          ·
            refine ⟨57062694180583025073281857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76083592240777366764375809 57062694180583025073281857)
            ·
              refine ⟨42797020635437268804961393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57062694180583025073281857 42797020635437268804961393)
              ·
                refine ⟨32097765476577951603721045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42797020635437268804961393 32097765476577951603721045)
                ·
                  refine ⟨188072844589323935178053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32097765476577951603721045 188072844589323935178053)
                  ·
                    rfl

theorem cell23_3296435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 9].length) (baseStart_3296435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296435 prefixEnd_3296435 := by exact prefixLift 3296435
  have htrace : WordTrace (prefixWord ++ tailWord_3296435) baseStart_3296435 baseEnd_3296435 := by
    simpa [prefixWord, tailWord_3296435, baseEnd_3296435] using wordTrace_append hprefix tailTrace_3296435
  have hstable : (prefixWord ++ tailWord_3296435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296435).length < 2 ^ (prefixWord ++ tailWord_3296435).sum := by decide
  have hdescent : baseEnd_3296435 < baseStart_3296435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296492 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 5]
def baseStart_3296492 : Nat := 118140960795 + 3296492 * 2 ^ 59
def prefixEnd_3296492 : Nat := 4983230072969 + 3 ^ 40 * 3296492 * 2
def baseEnd_3296492 : Nat := 1692684869701221693589715

theorem tailTrace_3296492 : CollatzResearch.WordTrace tailWord_3296492 prefixEnd_3296492 1692684869701221693589715 := by
  unfold tailWord_3296492
  simp only [CollatzResearch.WordTrace]
  refine ⟨60116470386689977428153865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80155293848919969904205153 60116470386689977428153865)
  ·
    refine ⟨45087352790017483071115399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60116470386689977428153865 45087352790017483071115399)
    ·
      refine ⟨67631029185026224606673099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45087352790017483071115399 67631029185026224606673099)
      ·
        refine ⟨101446543777539336910009649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67631029185026224606673099 101446543777539336910009649)
        ·
          refine ⟨76084907833154502682507237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101446543777539336910009649 76084907833154502682507237)
          ·
            refine ⟨14265920218716469252970107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76084907833154502682507237 14265920218716469252970107)
            ·
              refine ⟨21398880328074703879455161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14265920218716469252970107 21398880328074703879455161)
              ·
                refine ⟨16049160246056027909591371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21398880328074703879455161 16049160246056027909591371)
                ·
                  refine ⟨24073740369084041864387057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16049160246056027909591371 24073740369084041864387057)
                  ·
                    refine ⟨18055305276813031398290293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24073740369084041864387057 18055305276813031398290293)
                    ·
                      refine ⟨1692684869701221693589715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18055305276813031398290293 1692684869701221693589715)
                      ·
                        rfl

theorem cell23_3296492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_3296492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296492 prefixEnd_3296492 := by exact prefixLift 3296492
  have htrace : WordTrace (prefixWord ++ tailWord_3296492) baseStart_3296492 baseEnd_3296492 := by
    simpa [prefixWord, tailWord_3296492, baseEnd_3296492] using wordTrace_append hprefix tailTrace_3296492
  have hstable : (prefixWord ++ tailWord_3296492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296492).length < 2 ^ (prefixWord ++ tailWord_3296492).sum := by decide
  have hdescent : baseEnd_3296492 < baseStart_3296492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296529 : List Nat := [1, 2, 2, 1, 1, 4, 3, 2, 3, 4]
def baseStart_3296529 : Nat := 118140960795 + 3296529 * 2 ^ 59
def prefixEnd_3296529 : Nat := 4983230072969 + 3 ^ 40 * 3296529 * 2
def baseEnd_3296529 : Nat := 564234622828479349609015

theorem tailTrace_3296529 : CollatzResearch.WordTrace tailWord_3296529 prefixEnd_3296529 564234622828479349609015 := by
  unfold tailWord_3296529
  simp only [CollatzResearch.WordTrace]
  refine ⟨120234290274245910175404641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80156193516163940116936427 120234290274245910175404641)
  ·
    refine ⟨90175717705684432631553481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120234290274245910175404641 90175717705684432631553481)
    ·
      refine ⟨67631788279263324473665111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90175717705684432631553481 67631788279263324473665111)
      ·
        refine ⟨101447682418894986710497667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67631788279263324473665111 101447682418894986710497667)
        ·
          refine ⟨152171523628342480065746501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101447682418894986710497667 152171523628342480065746501)
          ·
            refine ⟨28532160680314215012327469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152171523628342480065746501 28532160680314215012327469)
            ·
              refine ⟨10699560255117830629622801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28532160680314215012327469 10699560255117830629622801)
              ·
                refine ⟨8024670191338372972217101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10699560255117830629622801 8024670191338372972217101)
                ·
                  refine ⟨3009251321751889864581413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8024670191338372972217101 3009251321751889864581413)
                  ·
                    refine ⟨564234622828479349609015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3009251321751889864581413 564234622828479349609015)
                    ·
                      rfl

theorem cell23_3296529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_3296529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296529 prefixEnd_3296529 := by exact prefixLift 3296529
  have htrace : WordTrace (prefixWord ++ tailWord_3296529) baseStart_3296529 baseEnd_3296529 := by
    simpa [prefixWord, tailWord_3296529, baseEnd_3296529] using wordTrace_append hprefix tailTrace_3296529
  have hstable : (prefixWord ++ tailWord_3296529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296529).length < 2 ^ (prefixWord ++ tailWord_3296529).sum := by decide
  have hdescent : baseEnd_3296529 < baseStart_3296529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296536 : List Nat := [2, 1, 2, 3, 1, 5, 1, 1, 2, 1, 4]
def baseStart_3296536 : Nat := 118140960795 + 3296536 * 2 ^ 59
def prefixEnd_3296536 : Nat := 4983230072969 + 3 ^ 40 * 3296536 * 2
def baseEnd_3296536 : Nat := 1692707462850019521439513

theorem tailTrace_3296536 : CollatzResearch.WordTrace tailWord_3296536 prefixEnd_3296536 1692707462850019521439513 := by
  unfold tailWord_3296536
  simp only [CollatzResearch.WordTrace]
  refine ⟨60117272792610275185454731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80156363723480366913939641 60117272792610275185454731)
  ·
    refine ⟨90175909188915412778182097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60117272792610275185454731 90175909188915412778182097)
    ·
      refine ⟨67631931891686559583636573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90175909188915412778182097 67631931891686559583636573)
      ·
        refine ⟨25361974459382459843863715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67631931891686559583636573 25361974459382459843863715)
        ·
          refine ⟨38042961689073689765795573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25361974459382459843863715 38042961689073689765795573)
          ·
            refine ⟨3566527658350658415543335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38042961689073689765795573 3566527658350658415543335)
            ·
              refine ⟨5349791487525987623315003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3566527658350658415543335 5349791487525987623315003)
              ·
                refine ⟨8024687231288981434972505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5349791487525987623315003 8024687231288981434972505)
                ·
                  refine ⟨6018515423466736076229379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8024687231288981434972505 6018515423466736076229379)
                  ·
                    refine ⟨9027773135200104114344069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6018515423466736076229379 9027773135200104114344069)
                    ·
                      refine ⟨1692707462850019521439513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9027773135200104114344069 1692707462850019521439513)
                      ·
                        rfl

theorem cell23_3296536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_3296536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296536 prefixEnd_3296536 := by exact prefixLift 3296536
  have htrace : WordTrace (prefixWord ++ tailWord_3296536) baseStart_3296536 baseEnd_3296536 := by
    simpa [prefixWord, tailWord_3296536, baseEnd_3296536] using wordTrace_append hprefix tailTrace_3296536
  have hstable : (prefixWord ++ tailWord_3296536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296536).length < 2 ^ (prefixWord ++ tailWord_3296536).sum := by decide
  have hdescent : baseEnd_3296536 < baseStart_3296536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296596 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 1, 5, 2]
def baseStart_3296596 : Nat := 118140960795 + 3296596 * 2 ^ 59
def prefixEnd_3296596 : Nat := 4983230072969 + 3 ^ 40 * 3296596 * 2
def baseEnd_3296596 : Nat := 1692738271689289286689237

theorem tailTrace_3296596 : CollatzResearch.WordTrace tailWord_3296596 prefixEnd_3296596 1692738271689289286689237 := by
  unfold tailWord_3296596
  simp only [CollatzResearch.WordTrace]
  refine ⟨60118366982501590309046821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80157822643335453745395761 60118366982501590309046821)
  ·
    refine ⟨11272193809219048182946279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60118366982501590309046821 11272193809219048182946279)
    ·
      refine ⟨16908290713828572274419419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11272193809219048182946279 16908290713828572274419419)
      ·
        refine ⟨25362436070742858411629129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16908290713828572274419419 25362436070742858411629129)
        ·
          refine ⟨19021827053057143808721847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25362436070742858411629129 19021827053057143808721847)
          ·
            refine ⟨28532740579585715713082771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19021827053057143808721847 28532740579585715713082771)
            ·
              refine ⟨42799110869378573569624157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28532740579585715713082771 42799110869378573569624157)
              ·
                refine ⟨16049666576016965088609059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42799110869378573569624157 16049666576016965088609059)
                ·
                  refine ⟨24074499864025447632913589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16049666576016965088609059 24074499864025447632913589)
                  ·
                    refine ⟨2256984362252385715585649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24074499864025447632913589 2256984362252385715585649)
                    ·
                      refine ⟨1692738271689289286689237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2256984362252385715585649 1692738271689289286689237)
                      ·
                        rfl

theorem cell23_3296596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_3296596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296596 prefixEnd_3296596 := by exact prefixLift 3296596
  have htrace : WordTrace (prefixWord ++ tailWord_3296596) baseStart_3296596 baseEnd_3296596 := by
    simpa [prefixWord, tailWord_3296596, baseEnd_3296596] using wordTrace_append hprefix tailTrace_3296596
  have hstable : (prefixWord ++ tailWord_3296596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296596).length < 2 ^ (prefixWord ++ tailWord_3296596).sum := by decide
  have hdescent : baseEnd_3296596 < baseStart_3296596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296636 : List Nat := [2, 2, 2, 1, 1, 1, 5, 3, 2, 4]
def baseStart_3296636 : Nat := 118140960795 + 3296636 * 2 ^ 59
def prefixEnd_3296636 : Nat := 4983230072969 + 3 ^ 40 * 3296636 * 2
def baseEnd_3296636 : Nat := 564252936971823043396351

theorem tailTrace_3296636 : CollatzResearch.WordTrace tailWord_3296636 prefixEnd_3296636 564252936971823043396351 := by
  unfold tailWord_3296636
  simp only [CollatzResearch.WordTrace]
  refine ⟨60119096442429133724774881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80158795256572178299699841 60119096442429133724774881)
  ·
    refine ⟨45089322331821850293581161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60119096442429133724774881 45089322331821850293581161)
    ·
      refine ⟨33816991748866387720185871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45089322331821850293581161 33816991748866387720185871)
      ·
        refine ⟨50725487623299581580278807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33816991748866387720185871 50725487623299581580278807)
        ·
          refine ⟨76088231434949372370418211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50725487623299581580278807 76088231434949372370418211)
          ·
            refine ⟨114132347152424058555627317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76088231434949372370418211 114132347152424058555627317)
            ·
              refine ⟨10699907545539755489590061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114132347152424058555627317 10699907545539755489590061)
              ·
                refine ⟨4012465329577408308596273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10699907545539755489590061 4012465329577408308596273)
                ·
                  refine ⟨3009348997183056231447205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4012465329577408308596273 3009348997183056231447205)
                  ·
                    refine ⟨564252936971823043396351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3009348997183056231447205 564252936971823043396351)
                    ·
                      rfl

theorem cell23_3296636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_3296636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296636 prefixEnd_3296636 := by exact prefixLift 3296636
  have htrace : WordTrace (prefixWord ++ tailWord_3296636) baseStart_3296636 baseEnd_3296636 := by
    simpa [prefixWord, tailWord_3296636, baseEnd_3296636] using wordTrace_append hprefix tailTrace_3296636
  have hstable : (prefixWord ++ tailWord_3296636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296636).length < 2 ^ (prefixWord ++ tailWord_3296636).sum := by decide
  have hdescent : baseEnd_3296636 < baseStart_3296636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296643 : List Nat := [1, 1, 1, 3, 5, 3, 1, 2, 1, 1, 4]
def baseStart_3296643 : Nat := 118140960795 + 3296643 * 2 ^ 59
def prefixEnd_3296643 : Nat := 4983230072969 + 3 ^ 40 * 3296643 * 2
def baseEnd_3296643 : Nat := 1692762405280050602801521

theorem tailTrace_3296643 : CollatzResearch.WordTrace tailWord_3296643 prefixEnd_3296643 1692762405280050602801521 := by
  unfold tailWord_3296643
  simp only [CollatzResearch.WordTrace]
  refine ⟨120238448195832907645054583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80158965463888605096703055 120238448195832907645054583)
  ·
    refine ⟨180357672293749361467581875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120238448195832907645054583 180357672293749361467581875)
    ·
      refine ⟨270536508440624042201372813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180357672293749361467581875 270536508440624042201372813)
      ·
        refine ⟨101451190665234015825514805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270536508440624042201372813 101451190665234015825514805)
        ·
          refine ⟨9511049124865688983642013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101451190665234015825514805 9511049124865688983642013)
          ·
            refine ⟨3566643421824633368865755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9511049124865688983642013 3566643421824633368865755)
            ·
              refine ⟨5349965132736950053298633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3566643421824633368865755 5349965132736950053298633)
              ·
                refine ⟨4012473849552712539973975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5349965132736950053298633 4012473849552712539973975)
                ·
                  refine ⟨6018710774329068809960963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4012473849552712539973975 6018710774329068809960963)
                  ·
                    refine ⟨9028066161493603214941445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6018710774329068809960963 9028066161493603214941445)
                    ·
                      refine ⟨1692762405280050602801521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9028066161493603214941445 1692762405280050602801521)
                      ·
                        rfl

theorem cell23_3296643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 1, 4].length) (baseStart_3296643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296643 prefixEnd_3296643 := by exact prefixLift 3296643
  have htrace : WordTrace (prefixWord ++ tailWord_3296643) baseStart_3296643 baseEnd_3296643 := by
    simpa [prefixWord, tailWord_3296643, baseEnd_3296643] using wordTrace_append hprefix tailTrace_3296643
  have hstable : (prefixWord ++ tailWord_3296643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296643).length < 2 ^ (prefixWord ++ tailWord_3296643).sum := by decide
  have hdescent : baseEnd_3296643 < baseStart_3296643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296660 : List Nat := [2, 4, 2, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_3296660 : Nat := 118140960795 + 3296660 * 2 ^ 59
def prefixEnd_3296660 : Nat := 4983230072969 + 3 ^ 40 * 3296660 * 2
def baseEnd_3296660 : Nat := 1692771134451177036288943

theorem tailTrace_3296660 : CollatzResearch.WordTrace tailWord_3296660 prefixEnd_3296660 1692771134451177036288943 := by
  unfold tailWord_3296660
  simp only [CollatzResearch.WordTrace]
  refine ⟨60119534118385659774211717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80159378824514213032282289 60119534118385659774211717)
  ·
    refine ⟨11272412647197311207664697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60119534118385659774211717 11272412647197311207664697)
    ·
      refine ⟨8454309485397983405748523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11272412647197311207664697 8454309485397983405748523)
      ·
        refine ⟨12681464228096975108622785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8454309485397983405748523 12681464228096975108622785)
        ·
          refine ⟨9511098171072731331467089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12681464228096975108622785 9511098171072731331467089)
          ·
            refine ⟨7133323628304548498600317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9511098171072731331467089 7133323628304548498600317)
            ·
              refine ⟨2674996360614205686975119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7133323628304548498600317 2674996360614205686975119)
              ·
                refine ⟨4012494540921308530462679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2674996360614205686975119 4012494540921308530462679)
                ·
                  refine ⟨6018741811381962795694019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4012494540921308530462679 6018741811381962795694019)
                  ·
                    refine ⟨9028112717072944193541029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6018741811381962795694019 9028112717072944193541029)
                    ·
                      refine ⟨1692771134451177036288943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9028112717072944193541029 1692771134451177036288943)
                      ·
                        rfl

theorem cell23_3296660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_3296660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296660 prefixEnd_3296660 := by exact prefixLift 3296660
  have htrace : WordTrace (prefixWord ++ tailWord_3296660) baseStart_3296660 baseEnd_3296660 := by
    simpa [prefixWord, tailWord_3296660, baseEnd_3296660] using wordTrace_append hprefix tailTrace_3296660
  have hstable : (prefixWord ++ tailWord_3296660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296660).length < 2 ^ (prefixWord ++ tailWord_3296660).sum := by decide
  have hdescent : baseEnd_3296660 < baseStart_3296660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296679 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 1, 9]
def baseStart_3296679 : Nat := 118140960795 + 3296679 * 2 ^ 59
def prefixEnd_3296679 : Nat := 4983230072969 + 3 ^ 40 * 3296679 * 2
def baseEnd_3296679 : Nat := 564260296861204153983785

theorem tailTrace_3296679 : CollatzResearch.WordTrace tailWord_3296679 prefixEnd_3296679 564260296861204153983785 := by
  unfold tailWord_3296679
  simp only [CollatzResearch.WordTrace]
  refine ⟨120239761223702485793365091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80159840815801657195576727 120239761223702485793365091)
  ·
    refine ⟨180359641835553728690047637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120239761223702485793365091 180359641835553728690047637)
    ·
      refine ⟨8454358211041581032345983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 180359641835553728690047637 8454358211041581032345983)
      ·
        refine ⟨12681537316562371548518975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8454358211041581032345983 12681537316562371548518975)
        ·
          refine ⟨19022305974843557322778463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12681537316562371548518975 19022305974843557322778463)
          ·
            refine ⟨28533458962265335984167695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19022305974843557322778463 28533458962265335984167695)
            ·
              refine ⟨42800188443398003976251543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28533458962265335984167695 42800188443398003976251543)
              ·
                refine ⟨64200282665097005964377315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42800188443398003976251543 64200282665097005964377315)
                ·
                  refine ⟨96300423997645508946565973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64200282665097005964377315 96300423997645508946565973)
                  ·
                    refine ⟨564260296861204153983785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 96300423997645508946565973 564260296861204153983785)
                    ·
                      rfl

theorem cell23_3296679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_3296679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296679 prefixEnd_3296679 := by exact prefixLift 3296679
  have htrace : WordTrace (prefixWord ++ tailWord_3296679) baseStart_3296679 baseEnd_3296679 := by
    simpa [prefixWord, tailWord_3296679, baseEnd_3296679] using wordTrace_append hprefix tailTrace_3296679
  have hstable : (prefixWord ++ tailWord_3296679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296679).length < 2 ^ (prefixWord ++ tailWord_3296679).sum := by decide
  have hdescent : baseEnd_3296679 < baseStart_3296679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296693 : List Nat := [1, 3, 3, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_3296693 : Nat := 118140960795 + 3296693 * 2 ^ 59
def prefixEnd_3296693 : Nat := 4983230072969 + 3 ^ 40 * 3296693 * 2
def baseEnd_3296693 : Nat := 1692788079312775407176291

theorem tailTrace_3296693 : CollatzResearch.WordTrace tailWord_3296693 prefixEnd_3296693 1692788079312775407176291 := by
  unfold tailWord_3296693
  simp only [CollatzResearch.WordTrace]
  refine ⟨120240271845651766184374733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80160181230434510789583155 120240271845651766184374733)
  ·
    refine ⟨45090101942119412319140525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120240271845651766184374733 45090101942119412319140525)
    ·
      refine ⟨16908788228294779619677697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45090101942119412319140525 16908788228294779619677697)
      ·
        refine ⟨12681591171221084714758273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16908788228294779619677697 12681591171221084714758273)
        ·
          refine ⟨9511193378415813536068705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12681591171221084714758273 9511193378415813536068705)
          ·
            refine ⟨7133395033811860152051529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9511193378415813536068705 7133395033811860152051529)
            ·
              refine ⟨5350046275358895114038647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7133395033811860152051529 5350046275358895114038647)
              ·
                refine ⟨8025069413038342671057971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5350046275358895114038647 8025069413038342671057971)
                ·
                  refine ⟨12037604119557514006586957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8025069413038342671057971 12037604119557514006586957)
                  ·
                    refine ⟨4514101544834067752470109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12037604119557514006586957 4514101544834067752470109)
                    ·
                      refine ⟨1692788079312775407176291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4514101544834067752470109 1692788079312775407176291)
                      ·
                        rfl

theorem cell23_3296693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_3296693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296693 prefixEnd_3296693 := by exact prefixLift 3296693
  have htrace : WordTrace (prefixWord ++ tailWord_3296693) baseStart_3296693 baseEnd_3296693 := by
    simpa [prefixWord, tailWord_3296693, baseEnd_3296693] using wordTrace_append hprefix tailTrace_3296693
  have hstable : (prefixWord ++ tailWord_3296693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296693).length < 2 ^ (prefixWord ++ tailWord_3296693).sum := by decide
  have hdescent : baseEnd_3296693 < baseStart_3296693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296719 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 5]
def baseStart_3296719 : Nat := 118140960795 + 3296719 * 2 ^ 59
def prefixEnd_3296719 : Nat := 4983230072969 + 3 ^ 40 * 3296719 * 2
def baseEnd_3296719 : Nat := 1692801429809792305451171

theorem tailTrace_3296719 : CollatzResearch.WordTrace tailWord_3296719 prefixEnd_3296719 1692801429809792305451171 := by
  unfold tailWord_3296719
  simp only [CollatzResearch.WordTrace]
  refine ⟨120241220143557572624821211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80160813429038381749880807 120241220143557572624821211)
  ·
    refine ⟨180361830215336358937231817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120241220143557572624821211 180361830215336358937231817)
    ·
      refine ⟨135271372661502269202923863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180361830215336358937231817 135271372661502269202923863)
      ·
        refine ⟨202907058992253403804385795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135271372661502269202923863 202907058992253403804385795)
        ·
          refine ⟨304360588488380105706578693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202907058992253403804385795 304360588488380105706578693)
          ·
            refine ⟨57067610341571269819983505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304360588488380105706578693 57067610341571269819983505)
            ·
              refine ⟨42800707756178452364987629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57067610341571269819983505 42800707756178452364987629)
              ·
                refine ⟨16050265408566919636870361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42800707756178452364987629 16050265408566919636870361)
                ·
                  refine ⟨12037699056425189727652771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16050265408566919636870361 12037699056425189727652771)
                  ·
                    refine ⟨18056548584637784591479157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12037699056425189727652771 18056548584637784591479157)
                    ·
                      refine ⟨1692801429809792305451171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18056548584637784591479157 1692801429809792305451171)
                      ·
                        rfl

theorem cell23_3296719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_3296719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296719 prefixEnd_3296719 := by exact prefixLift 3296719
  have htrace : WordTrace (prefixWord ++ tailWord_3296719) baseStart_3296719 baseEnd_3296719 := by
    simpa [prefixWord, tailWord_3296719, baseEnd_3296719] using wordTrace_append hprefix tailTrace_3296719
  have hstable : (prefixWord ++ tailWord_3296719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296719).length < 2 ^ (prefixWord ++ tailWord_3296719).sum := by decide
  have hdescent : baseEnd_3296719 < baseStart_3296719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296796 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_3296796 : Nat := 118140960795 + 3296796 * 2 ^ 59
def prefixEnd_3296796 : Nat := 4983230072969 + 3 ^ 40 * 3296796 * 2
def baseEnd_3296796 : Nat := 1692840967820188504188317

theorem tailTrace_3296796 : CollatzResearch.WordTrace tailWord_3296796 prefixEnd_3296796 1692840967820188504188317 := by
  unfold tailWord_3296796
  simp only [CollatzResearch.WordTrace]
  refine ⟨60122014282139307387687121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80162685709519076516916161 60122014282139307387687121)
  ·
    refine ⟨45091510711604480540765341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60122014282139307387687121 45091510711604480540765341)
    ·
      refine ⟨16909316516851680202787003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45091510711604480540765341 16909316516851680202787003)
      ·
        refine ⟨25363974775277520304180505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16909316516851680202787003 25363974775277520304180505)
        ·
          refine ⟨19022981081458140228135379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25363974775277520304180505 19022981081458140228135379)
          ·
            refine ⟨28534471622187210342203069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19022981081458140228135379 28534471622187210342203069)
            ·
              refine ⟨10700426858320203878326151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28534471622187210342203069 10700426858320203878326151)
              ·
                refine ⟨16050640287480305817489227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10700426858320203878326151 16050640287480305817489227)
                ·
                  refine ⟨24075960431220458726233841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16050640287480305817489227 24075960431220458726233841)
                  ·
                    refine ⟨18056970323415344044675381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24075960431220458726233841 18056970323415344044675381)
                    ·
                      refine ⟨1692840967820188504188317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18056970323415344044675381 1692840967820188504188317)
                      ·
                        rfl

theorem cell23_3296796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_3296796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296796 prefixEnd_3296796 := by exact prefixLift 3296796
  have htrace : WordTrace (prefixWord ++ tailWord_3296796) baseStart_3296796 baseEnd_3296796 := by
    simpa [prefixWord, tailWord_3296796, baseEnd_3296796] using wordTrace_append hprefix tailTrace_3296796
  have hstable : (prefixWord ++ tailWord_3296796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296796).length < 2 ^ (prefixWord ++ tailWord_3296796).sum := by decide
  have hdescent : baseEnd_3296796 < baseStart_3296796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296816 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 5, 4]
def baseStart_3296816 : Nat := 118140960795 + 3296816 * 2 ^ 59
def prefixEnd_3296816 : Nat := 4983230072969 + 3 ^ 40 * 3296816 * 2
def baseEnd_3296816 : Nat := 564283745811092808646075

theorem tailTrace_3296816 : CollatzResearch.WordTrace tailWord_3296816 prefixEnd_3296816 564283745811092808646075 := by
  unfold tailWord_3296816
  simp only [CollatzResearch.WordTrace]
  refine ⟨60122379012103079095551151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80163172016137438794068201 60122379012103079095551151)
  ·
    refine ⟨90183568518154618643326727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60122379012103079095551151 90183568518154618643326727)
    ·
      refine ⟨135275352777231927964990091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90183568518154618643326727 135275352777231927964990091)
      ·
        refine ⟨202913029165847891947485137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135275352777231927964990091 202913029165847891947485137)
        ·
          refine ⟨152184771874385918960613853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202913029165847891947485137 152184771874385918960613853)
          ·
            refine ⟨57069289452894719610230195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152184771874385918960613853 57069289452894719610230195)
            ·
              refine ⟨85603934179342079415345293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57069289452894719610230195 85603934179342079415345293)
              ·
                refine ⟨32101475317253279780754485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85603934179342079415345293 32101475317253279780754485)
                ·
                  refine ⟨3009513310992494979445733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32101475317253279780754485 3009513310992494979445733)
                  ·
                    refine ⟨564283745811092808646075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3009513310992494979445733 564283745811092808646075)
                    ·
                      rfl

theorem cell23_3296816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 5, 4].length) (baseStart_3296816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296816 prefixEnd_3296816 := by exact prefixLift 3296816
  have htrace : WordTrace (prefixWord ++ tailWord_3296816) baseStart_3296816 baseEnd_3296816 := by
    simpa [prefixWord, tailWord_3296816, baseEnd_3296816] using wordTrace_append hprefix tailTrace_3296816
  have hstable : (prefixWord ++ tailWord_3296816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296816).length < 2 ^ (prefixWord ++ tailWord_3296816).sum := by decide
  have hdescent : baseEnd_3296816 < baseStart_3296816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296823 : List Nat := [1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 4]
def baseStart_3296823 : Nat := 118140960795 + 3296823 * 2 ^ 59
def prefixEnd_3296823 : Nat := 4983230072969 + 3 ^ 40 * 3296823 * 2
def baseEnd_3296823 : Nat := 1692854831797859898550693

theorem tailTrace_3296823 : CollatzResearch.WordTrace tailWord_3296823 prefixEnd_3296823 1692854831797859898550693 := by
  unfold tailWord_3296823
  simp only [CollatzResearch.WordTrace]
  refine ⟨120245013335180798386607123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80163342223453865591071415 120245013335180798386607123)
  ·
    refine ⟨180367520002771197579910685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120245013335180798386607123 180367520002771197579910685)
    ·
      refine ⟨67637820001039199092466507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180367520002771197579910685 67637820001039199092466507)
      ·
        refine ⟨101456730001558798638699761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67637820001039199092466507 101456730001558798638699761)
        ·
          refine ⟨76092547501169098979024821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101456730001558798638699761 76092547501169098979024821)
          ·
            refine ⟨7133676328234603029283577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76092547501169098979024821 7133676328234603029283577)
            ·
              refine ⟨5350257246175952271962683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7133676328234603029283577 5350257246175952271962683)
              ·
                refine ⟨8025385869263928407944025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5350257246175952271962683 8025385869263928407944025)
                ·
                  refine ⟨6019039401947946305958019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8025385869263928407944025 6019039401947946305958019)
                  ·
                    refine ⟨9028559102921919458937029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6019039401947946305958019 9028559102921919458937029)
                    ·
                      refine ⟨1692854831797859898550693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9028559102921919458937029 1692854831797859898550693)
                      ·
                        rfl

theorem cell23_3296823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_3296823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296823 prefixEnd_3296823 := by exact prefixLift 3296823
  have htrace : WordTrace (prefixWord ++ tailWord_3296823) baseStart_3296823 baseEnd_3296823 := by
    simpa [prefixWord, tailWord_3296823, baseEnd_3296823] using wordTrace_append hprefix tailTrace_3296823
  have hstable : (prefixWord ++ tailWord_3296823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296823).length < 2 ^ (prefixWord ++ tailWord_3296823).sum := by decide
  have hdescent : baseEnd_3296823 < baseStart_3296823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296856 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 2, 5, 3]
def baseStart_3296856 : Nat := 118140960795 + 3296856 * 2 ^ 59
def prefixEnd_3296856 : Nat := 4983230072969 + 3 ^ 40 * 3296856 * 2
def baseEnd_3296856 : Nat := 1692871776659458269438041

theorem tailTrace_3296856 : CollatzResearch.WordTrace tailWord_3296856 prefixEnd_3296856 1692871776659458269438041 := by
  unfold tailWord_3296856
  simp only [CollatzResearch.WordTrace]
  refine ⟨60123108472030622511279211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80164144629374163348372281 60123108472030622511279211)
  ·
    refine ⟨90184662708045933766918817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60123108472030622511279211 90184662708045933766918817)
    ·
      refine ⟨67638497031034450325189113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90184662708045933766918817 67638497031034450325189113)
      ·
        refine ⟨50728872773275837743891835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67638497031034450325189113 50728872773275837743891835)
        ·
          refine ⟨76093309159913756615837753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50728872773275837743891835 76093309159913756615837753)
          ·
            refine ⟨57069981869935317461878315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76093309159913756615837753 57069981869935317461878315)
            ·
              refine ⟨85604972804902976192817473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57069981869935317461878315 85604972804902976192817473)
              ·
                refine ⟨64203729603677232144613105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85604972804902976192817473 64203729603677232144613105)
                ·
                  refine ⟨48152797202757924108459829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64203729603677232144613105 48152797202757924108459829)
                  ·
                    refine ⟨4514324737758555385168109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48152797202757924108459829 4514324737758555385168109)
                    ·
                      refine ⟨1692871776659458269438041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4514324737758555385168109 1692871776659458269438041)
                      ·
                        rfl

theorem cell23_3296856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_3296856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296856 prefixEnd_3296856 := by exact prefixLift 3296856
  have htrace : WordTrace (prefixWord ++ tailWord_3296856) baseStart_3296856 baseEnd_3296856 := by
    simpa [prefixWord, tailWord_3296856, baseEnd_3296856] using wordTrace_append hprefix tailTrace_3296856
  have hstable : (prefixWord ++ tailWord_3296856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296856).length < 2 ^ (prefixWord ++ tailWord_3296856).sum := by decide
  have hdescent : baseEnd_3296856 < baseStart_3296856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296873 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 5, 1, 3]
def baseStart_3296873 : Nat := 118140960795 + 3296873 * 2 ^ 59
def prefixEnd_3296873 : Nat := 4983230072969 + 3 ^ 40 * 3296873 * 2
def baseEnd_3296873 : Nat := 1692880505830584702925463

theorem tailTrace_3296873 : CollatzResearch.WordTrace tailWord_3296873 prefixEnd_3296873 1692880505830584702925463 := by
  unfold tailWord_3296873
  simp only [CollatzResearch.WordTrace]
  refine ⟨120246836984999656925927273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80164557989999771283951515 120246836984999656925927273)
  ·
    refine ⟨90185127738749742694445455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120246836984999656925927273 90185127738749742694445455)
    ·
      refine ⟨135277691608124614041668183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90185127738749742694445455 135277691608124614041668183)
      ·
        refine ⟨202916537412186921062502275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135277691608124614041668183 202916537412186921062502275)
        ·
          refine ⟨304374806118280381593753413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202916537412186921062502275 304374806118280381593753413)
          ·
            refine ⟨57070276147177571548828765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304374806118280381593753413 57070276147177571548828765)
            ·
              refine ⟨21401353555191589330810787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57070276147177571548828765 21401353555191589330810787)
              ·
                refine ⟨32102030332787383996216181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21401353555191589330810787 32102030332787383996216181)
                ·
                  refine ⟨3009565343698817249645267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32102030332787383996216181 3009565343698817249645267)
                  ·
                    refine ⟨4514348015548225874467901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3009565343698817249645267 4514348015548225874467901)
                    ·
                      refine ⟨1692880505830584702925463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4514348015548225874467901 1692880505830584702925463)
                      ·
                        rfl

theorem cell23_3296873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 1, 3].length) (baseStart_3296873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296873 prefixEnd_3296873 := by exact prefixLift 3296873
  have htrace : WordTrace (prefixWord ++ tailWord_3296873) baseStart_3296873 baseEnd_3296873 := by
    simpa [prefixWord, tailWord_3296873, baseEnd_3296873] using wordTrace_append hprefix tailTrace_3296873
  have hstable : (prefixWord ++ tailWord_3296873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296873).length < 2 ^ (prefixWord ++ tailWord_3296873).sum := by decide
  have hdescent : baseEnd_3296873 < baseStart_3296873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296877 : List Nat := [1, 5, 1, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_3296877 : Nat := 118140960795 + 3296877 * 2 ^ 59
def prefixEnd_3296877 : Nat := 4983230072969 + 3 ^ 40 * 3296877 * 2
def baseEnd_3296877 : Nat := 1692882559753202687275445

theorem tailTrace_3296877 : CollatzResearch.WordTrace tailWord_3296877 prefixEnd_3296877 1692882559753202687275445 := by
  unfold tailWord_3296877
  simp only [CollatzResearch.WordTrace]
  refine ⟨120246982876985165609072885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80164655251323443739381923 120246982876985165609072885)
  ·
    refine ⟨11273154644717359275850583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120246982876985165609072885 11273154644717359275850583)
    ·
      refine ⟨16909731967076038913775875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11273154644717359275850583 16909731967076038913775875)
      ·
        refine ⟨25364597950614058370663813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16909731967076038913775875 25364597950614058370663813)
        ·
          refine ⟨4755862115740135944499465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25364597950614058370663813 4755862115740135944499465)
          ·
            refine ⟨3566896586805101958374599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4755862115740135944499465 3566896586805101958374599)
            ·
              refine ⟨5350344880207652937561899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3566896586805101958374599 5350344880207652937561899)
              ·
                refine ⟨8025517320311479406342849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5350344880207652937561899 8025517320311479406342849)
                ·
                  refine ⟨6019137990233609554757137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8025517320311479406342849 6019137990233609554757137)
                  ·
                    refine ⟨4514353492675207166067853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6019137990233609554757137 4514353492675207166067853)
                    ·
                      refine ⟨1692882559753202687275445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4514353492675207166067853 1692882559753202687275445)
                      ·
                        rfl

theorem cell23_3296877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_3296877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296877 prefixEnd_3296877 := by exact prefixLift 3296877
  have htrace : WordTrace (prefixWord ++ tailWord_3296877) baseStart_3296877 baseEnd_3296877 := by
    simpa [prefixWord, tailWord_3296877, baseEnd_3296877] using wordTrace_append hprefix tailTrace_3296877
  have hstable : (prefixWord ++ tailWord_3296877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296877).length < 2 ^ (prefixWord ++ tailWord_3296877).sum := by decide
  have hdescent : baseEnd_3296877 < baseStart_3296877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296927 : List Nat := [1, 1, 2, 7, 1, 1, 2, 2, 1, 5]
def baseStart_3296927 : Nat := 118140960795 + 3296927 * 2 ^ 59
def prefixEnd_3296927 : Nat := 4983230072969 + 3 ^ 40 * 3296927 * 2
def baseEnd_3296927 : Nat := 564302744595309163883405

theorem tailTrace_3296927 : CollatzResearch.WordTrace tailWord_3296927 prefixEnd_3296927 564302744595309163883405 := by
  unfold tailWord_3296927
  simp only [CollatzResearch.WordTrace]
  refine ⟨120248806526804024148393035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80165871017869349432262023 120248806526804024148393035)
  ·
    refine ⟨180373209790206036222589553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120248806526804024148393035 180373209790206036222589553)
    ·
      refine ⟨135279907342654527166942165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180373209790206036222589553 135279907342654527166942165)
      ·
        refine ⟨3170622828343465480475207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 135279907342654527166942165 3170622828343465480475207)
        ·
          refine ⟨4755934242515198220712811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3170622828343465480475207 4755934242515198220712811)
          ·
            refine ⟨7133901363772797331069217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4755934242515198220712811 7133901363772797331069217)
            ·
              refine ⟨5350426022829597998301913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7133901363772797331069217 5350426022829597998301913)
              ·
                refine ⟨4012819517122198498726435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5350426022829597998301913 4012819517122198498726435)
                ·
                  refine ⟨6019229275683297748089653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4012819517122198498726435 6019229275683297748089653)
                  ·
                    refine ⟨564302744595309163883405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6019229275683297748089653 564302744595309163883405)
                    ·
                      rfl

theorem cell23_3296927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 5].length) (baseStart_3296927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296927 prefixEnd_3296927 := by exact prefixLift 3296927
  have htrace : WordTrace (prefixWord ++ tailWord_3296927) baseStart_3296927 baseEnd_3296927 := by
    simpa [prefixWord, tailWord_3296927, baseEnd_3296927] using wordTrace_append hprefix tailTrace_3296927
  have hstable : (prefixWord ++ tailWord_3296927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296927).length < 2 ^ (prefixWord ++ tailWord_3296927).sum := by decide
  have hdescent : baseEnd_3296927 < baseStart_3296927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296933 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 3, 2, 3]
def baseStart_3296933 : Nat := 118140960795 + 3296933 * 2 ^ 59
def prefixEnd_3296933 : Nat := 4983230072969 + 3 ^ 40 * 3296933 * 2
def baseEnd_3296933 : Nat := 1692911314669854468175187

theorem tailTrace_3296933 : CollatzResearch.WordTrace tailWord_3296933 prefixEnd_3296933 1692911314669854468175187 := by
  unfold tailWord_3296933
  simp only [CollatzResearch.WordTrace]
  refine ⟨120249025364782287173111453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80166016909854858115407635 120249025364782287173111453)
  ·
    refine ⟨45093384511793357689916795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120249025364782287173111453 45093384511793357689916795)
    ·
      refine ⟨67640076767690036534875193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45093384511793357689916795 67640076767690036534875193)
      ·
        refine ⟨50730057575767527401156395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67640076767690036534875193 50730057575767527401156395)
        ·
          refine ⟨76095086363651291101734593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50730057575767527401156395 76095086363651291101734593)
          ·
            refine ⟨57071314772738468326300945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76095086363651291101734593 57071314772738468326300945)
            ·
              refine ⟨42803486079553851244725709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57071314772738468326300945 42803486079553851244725709)
              ·
                refine ⟨16051307279832694216772141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42803486079553851244725709 16051307279832694216772141)
                ·
                  refine ⟨6019240229937260331289553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16051307279832694216772141 6019240229937260331289553)
                  ·
                    refine ⟨4514430172452945248467165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6019240229937260331289553 4514430172452945248467165)
                    ·
                      refine ⟨1692911314669854468175187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4514430172452945248467165 1692911314669854468175187)
                      ·
                        rfl

theorem cell23_3296933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_3296933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296933 prefixEnd_3296933 := by exact prefixLift 3296933
  have htrace : WordTrace (prefixWord ++ tailWord_3296933) baseStart_3296933 baseEnd_3296933 := by
    simpa [prefixWord, tailWord_3296933, baseEnd_3296933] using wordTrace_append hprefix tailTrace_3296933
  have hstable : (prefixWord ++ tailWord_3296933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296933).length < 2 ^ (prefixWord ++ tailWord_3296933).sum := by decide
  have hdescent : baseEnd_3296933 < baseStart_3296933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296976 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 5]
def baseStart_3296976 : Nat := 118140960795 + 3296976 * 2 ^ 59
def prefixEnd_3296976 : Nat := 4983230072969 + 3 ^ 40 * 3296976 * 2
def baseEnd_3296976 : Nat := 1692933394337997799937489

theorem tailTrace_3296976 : CollatzResearch.WordTrace tailWord_3296976 prefixEnd_3296976 1692933394337997799937489 := by
  unfold tailWord_3296976
  simp only [CollatzResearch.WordTrace]
  refine ⟨60125296851813252758463391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80167062469084337011284521 60125296851813252758463391)
  ·
    refine ⟨90187945277719879137695087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60125296851813252758463391 90187945277719879137695087)
    ·
      refine ⟨135281917916579818706542631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90187945277719879137695087 135281917916579818706542631)
      ·
        refine ⟨202922876874869728059813947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135281917916579818706542631 202922876874869728059813947)
        ·
          refine ⟨304384315312304592089720921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202922876874869728059813947 304384315312304592089720921)
          ·
            refine ⟨228288236484228444067290691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304384315312304592089720921 228288236484228444067290691)
            ·
              refine ⟨342432354726342666100936037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228288236484228444067290691 342432354726342666100936037)
              ·
                refine ⟨64206066511189249893925507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 342432354726342666100936037 64206066511189249893925507)
                ·
                  refine ⟨96309099766783874840888261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64206066511189249893925507 96309099766783874840888261)
                  ·
                    refine ⟨18057956206271976532666549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96309099766783874840888261 18057956206271976532666549)
                    ·
                      refine ⟨1692933394337997799937489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18057956206271976532666549 1692933394337997799937489)
                      ·
                        rfl

theorem cell23_3296976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_3296976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3296976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3296976 prefixEnd_3296976 := by exact prefixLift 3296976
  have htrace : WordTrace (prefixWord ++ tailWord_3296976) baseStart_3296976 baseEnd_3296976 := by
    simpa [prefixWord, tailWord_3296976, baseEnd_3296976] using wordTrace_append hprefix tailTrace_3296976
  have hstable : (prefixWord ++ tailWord_3296976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296976).length < 2 ^ (prefixWord ++ tailWord_3296976).sum := by decide
  have hdescent : baseEnd_3296976 < baseStart_3296976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297014 : List Nat := [5, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_3297014 : Nat := 118140960795 + 3297014 * 2 ^ 59
def prefixEnd_3297014 : Nat := 4983230072969 + 3 ^ 40 * 3297014 * 2
def baseEnd_3297014 : Nat := 1692952906602868651262315

theorem tailTrace_3297014 : CollatzResearch.WordTrace tailWord_3297014 prefixEnd_3297014 1692952906602868651262315 := by
  unfold tailWord_3297014
  simp only [CollatzResearch.WordTrace]
  refine ⟨7515748729843052375425631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80167986451659225337873397 7515748729843052375425631)
  ·
    refine ⟨11273623094764578563138447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7515748729843052375425631 11273623094764578563138447)
    ·
      refine ⟨16910434642146867844707671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11273623094764578563138447 16910434642146867844707671)
      ·
        refine ⟨25365651963220301767061507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16910434642146867844707671 25365651963220301767061507)
        ·
          refine ⟨38048477944830452650592261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25365651963220301767061507 38048477944830452650592261)
          ·
            refine ⟨7134089614655709871986049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38048477944830452650592261 7134089614655709871986049)
            ·
              refine ⟨5350567210991782403989537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7134089614655709871986049 5350567210991782403989537)
              ·
                refine ⟨4012925408243836802992153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5350567210991782403989537 4012925408243836802992153)
                ·
                  refine ⟨3009694056182877602244115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4012925408243836802992153 3009694056182877602244115)
                  ·
                    refine ⟨4514541084274316403366173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3009694056182877602244115 4514541084274316403366173)
                    ·
                      refine ⟨1692952906602868651262315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4514541084274316403366173 1692952906602868651262315)
                      ·
                        rfl

theorem cell23_3297014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_3297014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297014 prefixEnd_3297014 := by exact prefixLift 3297014
  have htrace : WordTrace (prefixWord ++ tailWord_3297014) baseStart_3297014 baseEnd_3297014 := by
    simpa [prefixWord, tailWord_3297014, baseEnd_3297014] using wordTrace_append hprefix tailTrace_3297014
  have hstable : (prefixWord ++ tailWord_3297014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297014).length < 2 ^ (prefixWord ++ tailWord_3297014).sum := by decide
  have hdescent : baseEnd_3297014 < baseStart_3297014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297020 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 3, 4, 2]
def baseStart_3297020 : Nat := 118140960795 + 3297020 * 2 ^ 59
def prefixEnd_3297020 : Nat := 4983230072969 + 3 ^ 40 * 3297020 * 2
def baseEnd_3297020 : Nat := 1692955987486795627787287

theorem tailTrace_3297020 : CollatzResearch.WordTrace tailWord_3297020 prefixEnd_3297020 1692955987486795627787287 := by
  unfold tailWord_3297020
  simp only [CollatzResearch.WordTrace]
  refine ⟨60126099257733550515764257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80168132343644734021019009 60126099257733550515764257)
  ·
    refine ⟨45094574443300162886823193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60126099257733550515764257 45094574443300162886823193)
    ·
      refine ⟨33820930832475122165117395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45094574443300162886823193 33820930832475122165117395)
      ·
        refine ⟨50731396248712683247676093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33820930832475122165117395 50731396248712683247676093)
        ·
          refine ⟨19024273593267256217878535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50731396248712683247676093 19024273593267256217878535)
          ·
            refine ⟨28536410389900884326817803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19024273593267256217878535 28536410389900884326817803)
            ·
              refine ⟨42804615584851326490226705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28536410389900884326817803 42804615584851326490226705)
              ·
                refine ⟨32103461688638494867670029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42804615584851326490226705 32103461688638494867670029)
                ·
                  refine ⟨12038798133239435575376261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32103461688638494867670029 12038798133239435575376261)
                  ·
                    refine ⟨2257274649982394170383049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12038798133239435575376261 2257274649982394170383049)
                    ·
                      refine ⟨1692955987486795627787287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2257274649982394170383049 1692955987486795627787287)
                      ·
                        rfl

theorem cell23_3297020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_3297020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297020 prefixEnd_3297020 := by exact prefixLift 3297020
  have htrace : WordTrace (prefixWord ++ tailWord_3297020) baseStart_3297020 baseEnd_3297020 := by
    simpa [prefixWord, tailWord_3297020, baseEnd_3297020] using wordTrace_append hprefix tailTrace_3297020
  have hstable : (prefixWord ++ tailWord_3297020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297020).length < 2 ^ (prefixWord ++ tailWord_3297020).sum := by decide
  have hdescent : baseEnd_3297020 < baseStart_3297020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297023 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 3]
def baseStart_3297023 : Nat := 118140960795 + 3297023 * 2 ^ 59
def prefixEnd_3297023 : Nat := 4983230072969 + 3 ^ 40 * 3297023 * 2
def baseEnd_3297023 : Nat := 1692957527928759116049773

theorem tailTrace_3297023 : CollatzResearch.WordTrace tailWord_3297023 prefixEnd_3297023 1692957527928759116049773 := by
  unfold tailWord_3297023
  simp only [CollatzResearch.WordTrace]
  refine ⟨120252307934456232543887723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80168205289637488362591815 120252307934456232543887723)
  ·
    refine ⟨180378461901684348815831585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120252307934456232543887723 180378461901684348815831585)
    ·
      refine ⟨135283846426263261611873689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180378461901684348815831585 135283846426263261611873689)
      ·
        refine ⟨101462884819697446208905267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135283846426263261611873689 101462884819697446208905267)
        ·
          refine ⟨152194327229546169313357901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101462884819697446208905267 152194327229546169313357901)
          ·
            refine ⟨57072872711079813492509213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152194327229546169313357901 57072872711079813492509213)
            ·
              refine ⟨21402327266654930059690955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57072872711079813492509213 21402327266654930059690955)
              ·
                refine ⟨32103490899982395089536433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21402327266654930059690955 32103490899982395089536433)
                ·
                  refine ⟨24077618174986796317152325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32103490899982395089536433 24077618174986796317152325)
                  ·
                    refine ⟨4514553407810024309466061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24077618174986796317152325 4514553407810024309466061)
                    ·
                      refine ⟨1692957527928759116049773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4514553407810024309466061 1692957527928759116049773)
                      ·
                        rfl

theorem cell23_3297023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_3297023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297023 prefixEnd_3297023 := by exact prefixLift 3297023
  have htrace : WordTrace (prefixWord ++ tailWord_3297023) baseStart_3297023 baseEnd_3297023 := by
    simpa [prefixWord, tailWord_3297023, baseEnd_3297023] using wordTrace_append hprefix tailTrace_3297023
  have hstable : (prefixWord ++ tailWord_3297023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297023).length < 2 ^ (prefixWord ++ tailWord_3297023).sum := by decide
  have hdescent : baseEnd_3297023 < baseStart_3297023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297093 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 3, 3, 4]
def baseStart_3297093 : Nat := 118140960795 + 3297093 * 2 ^ 59
def prefixEnd_3297093 : Nat := 4983230072969 + 3 ^ 40 * 3297093 * 2
def baseEnd_3297093 : Nat := 1692993471574573842174451

theorem tailTrace_3297093 : CollatzResearch.WordTrace tailWord_3297093 prefixEnd_3297093 1692993471574573842174451 := by
  unfold tailWord_3297093
  simp only [CollatzResearch.WordTrace]
  refine ⟨120254861044202634498935933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80169907362801756332623955 120254861044202634498935933)
  ·
    refine ⟨45095572891575987937100975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120254861044202634498935933 45095572891575987937100975)
    ·
      refine ⟨67643359337363981905651463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45095572891575987937100975 67643359337363981905651463)
      ·
        refine ⟨101465039006045972858477195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67643359337363981905651463 101465039006045972858477195)
        ·
          refine ⟨152197558509068959287715793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101465039006045972858477195 152197558509068959287715793)
          ·
            refine ⟨114148168881801719465786845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152197558509068959287715793 114148168881801719465786845)
            ·
              refine ⟨42805563330675644799670067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114148168881801719465786845 42805563330675644799670067)
              ·
                refine ⟨64208344996013467199505101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42805563330675644799670067 64208344996013467199505101)
                ·
                  refine ⟨24078129373505050199814413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64208344996013467199505101 24078129373505050199814413)
                  ·
                    refine ⟨9029298515064393824930405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24078129373505050199814413 9029298515064393824930405)
                    ·
                      refine ⟨1692993471574573842174451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9029298515064393824930405 1692993471574573842174451)
                      ·
                        rfl

theorem cell23_3297093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_3297093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297093 prefixEnd_3297093 := by exact prefixLift 3297093
  have htrace : WordTrace (prefixWord ++ tailWord_3297093) baseStart_3297093 baseEnd_3297093 := by
    simpa [prefixWord, tailWord_3297093, baseEnd_3297093] using wordTrace_append hprefix tailTrace_3297093
  have hstable : (prefixWord ++ tailWord_3297093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297093).length < 2 ^ (prefixWord ++ tailWord_3297093).sum := by decide
  have hdescent : baseEnd_3297093 < baseStart_3297093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297251 : List Nat := [1, 1, 1, 6, 1, 3, 2, 1, 3, 2, 2]
def baseStart_3297251 : Nat := 118140960795 + 3297251 * 2 ^ 59
def prefixEnd_3297251 : Nat := 4983230072969 + 3 ^ 40 * 3297251 * 2
def baseEnd_3297251 : Nat := 1693074601517984223998725

theorem tailTrace_3297251 : CollatzResearch.WordTrace tailWord_3297251 prefixEnd_3297251 1693074601517984223998725 := by
  unfold tailWord_3297251
  simp only [CollatzResearch.WordTrace]
  refine ⟨120260623777630227483187607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80173749185086818322125071 120260623777630227483187607)
  ·
    refine ⟨180390935666445341224781411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120260623777630227483187607 180390935666445341224781411)
    ·
      refine ⟨270586403499668011837172117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180390935666445341224781411 270586403499668011837172117)
      ·
        refine ⟨12683737664046938054867443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 270586403499668011837172117 12683737664046938054867443)
        ·
          refine ⟨19025606496070407082301165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12683737664046938054867443 19025606496070407082301165)
          ·
            refine ⟨7134602436026402655862937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19025606496070407082301165 7134602436026402655862937)
            ·
              refine ⟨5350951827019801991897203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7134602436026402655862937 5350951827019801991897203)
              ·
                refine ⟨8026427740529702987845805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5350951827019801991897203 8026427740529702987845805)
                ·
                  refine ⟨3009910402698638620442177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8026427740529702987845805 3009910402698638620442177)
                  ·
                    refine ⟨2257432802023978965331633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3009910402698638620442177 2257432802023978965331633)
                    ·
                      refine ⟨1693074601517984223998725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2257432802023978965331633 1693074601517984223998725)
                      ·
                        rfl

theorem cell23_3297251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_3297251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297251 prefixEnd_3297251 := by exact prefixLift 3297251
  have htrace : WordTrace (prefixWord ++ tailWord_3297251) baseStart_3297251 baseEnd_3297251 := by
    simpa [prefixWord, tailWord_3297251, baseEnd_3297251] using wordTrace_append hprefix tailTrace_3297251
  have hstable : (prefixWord ++ tailWord_3297251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297251).length < 2 ^ (prefixWord ++ tailWord_3297251).sum := by decide
  have hdescent : baseEnd_3297251 < baseStart_3297251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297261 : List Nat := [1, 5, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_3297261 : Nat := 118140960795 + 3297261 * 2 ^ 59
def prefixEnd_3297261 : Nat := 4983230072969 + 3 ^ 40 * 3297261 * 2
def baseEnd_3297261 : Nat := 564359912108176394957893

theorem tailTrace_3297261 : CollatzResearch.WordTrace tailWord_3297261 prefixEnd_3297261 564359912108176394957893 := by
  unfold tailWord_3297261
  simp only [CollatzResearch.WordTrace]
  refine ⟨120260988507593999191051637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80173992338395999460701091 120260988507593999191051637)
  ·
    refine ⟨11274467672586937424161091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120260988507593999191051637 11274467672586937424161091)
    ·
      refine ⟨16911701508880406136241637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11274467672586937424161091 16911701508880406136241637)
      ·
        refine ⟨3170944032915076150545307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16911701508880406136241637 3170944032915076150545307)
        ·
          refine ⟨4756416049372614225817961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3170944032915076150545307 4756416049372614225817961)
          ·
            refine ⟨3567312037029460669363471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4756416049372614225817961 3567312037029460669363471)
            ·
              refine ⟨5350968055544191004045207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3567312037029460669363471 5350968055544191004045207)
              ·
                refine ⟨8026452083316286506067811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5350968055544191004045207 8026452083316286506067811)
                ·
                  refine ⟨12039678124974429759101717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8026452083316286506067811 12039678124974429759101717)
                  ·
                    refine ⟨564359912108176394957893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12039678124974429759101717 564359912108176394957893)
                    ·
                      rfl

theorem cell23_3297261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_3297261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297261 prefixEnd_3297261 := by exact prefixLift 3297261
  have htrace : WordTrace (prefixWord ++ tailWord_3297261) baseStart_3297261 baseEnd_3297261 := by
    simpa [prefixWord, tailWord_3297261, baseEnd_3297261] using wordTrace_append hprefix tailTrace_3297261
  have hstable : (prefixWord ++ tailWord_3297261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297261).length < 2 ^ (prefixWord ++ tailWord_3297261).sum := by decide
  have hdescent : baseEnd_3297261 < baseStart_3297261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297307 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 5, 4, 2]
def baseStart_3297307 : Nat := 118140960795 + 3297307 * 2 ^ 59
def prefixEnd_3297307 : Nat := 4983230072969 + 3 ^ 40 * 3297307 * 2
def baseEnd_3297307 : Nat := 1693103356434636004898467

theorem tailTrace_3297307 : CollatzResearch.WordTrace tailWord_3297307 prefixEnd_3297307 1693103356434636004898467 := by
  unfold tailWord_3297307
  simp only [CollatzResearch.WordTrace]
  refine ⟨120262666265427349047226175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80175110843618232698150783 120262666265427349047226175)
  ·
    refine ⟨180393999398141023570839263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120262666265427349047226175 180393999398141023570839263)
    ·
      refine ⟨270590999097211535356258895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180393999398141023570839263 270590999097211535356258895)
      ·
        refine ⟨405886498645817303034388343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270590999097211535356258895 405886498645817303034388343)
        ·
          refine ⟨608829747968725954551582515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405886498645817303034388343 608829747968725954551582515)
          ·
            refine ⟨913244621953088931827373773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608829747968725954551582515 913244621953088931827373773)
            ·
              refine ⟨342466733232408349435265165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 913244621953088931827373773 342466733232408349435265165)
              ·
                refine ⟨128425024962153131038224437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342466733232408349435265165 128425024962153131038224437)
                ·
                  refine ⟨12039846090201856034833541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128425024962153131038224437 12039846090201856034833541)
                  ·
                    refine ⟨2257471141912848006531289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12039846090201856034833541 2257471141912848006531289)
                    ·
                      refine ⟨1693103356434636004898467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2257471141912848006531289 1693103356434636004898467)
                      ·
                        rfl

theorem cell23_3297307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 4, 2].length) (baseStart_3297307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297307 prefixEnd_3297307 := by exact prefixLift 3297307
  have htrace : WordTrace (prefixWord ++ tailWord_3297307) baseStart_3297307 baseEnd_3297307 := by
    simpa [prefixWord, tailWord_3297307, baseEnd_3297307] using wordTrace_append hprefix tailTrace_3297307
  have hstable : (prefixWord ++ tailWord_3297307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297307).length < 2 ^ (prefixWord ++ tailWord_3297307).sum := by decide
  have hdescent : baseEnd_3297307 < baseStart_3297307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297324 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 6, 2, 2]
def baseStart_3297324 : Nat := 118140960795 + 3297324 * 2 ^ 59
def prefixEnd_3297324 : Nat := 4983230072969 + 3 ^ 40 * 3297324 * 2
def baseEnd_3297324 : Nat := 1693112085605762438385889

theorem tailTrace_3297324 : CollatzResearch.WordTrace tailWord_3297324 prefixEnd_3297324 1693112085605762438385889 := by
  unfold tailWord_3297324
  simp only [CollatzResearch.WordTrace]
  refine ⟨60131643153182880475297513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80175524204243840633730017 60131643153182880475297513)
  ·
    refine ⟨45098732364887160356473135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60131643153182880475297513 45098732364887160356473135)
    ·
      refine ⟨67648098547330740534709703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45098732364887160356473135 67648098547330740534709703)
      ·
        refine ⟨101472147820996110802064555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67648098547330740534709703 101472147820996110802064555)
        ·
          refine ⟨152208221731494166203096833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101472147820996110802064555 152208221731494166203096833)
          ·
            refine ⟨114156166298620624652322625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152208221731494166203096833 114156166298620624652322625)
            ·
              refine ⟨85617124723965468489241969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114156166298620624652322625 85617124723965468489241969)
              ·
                refine ⟨64212843542974101366931477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85617124723965468489241969 64212843542974101366931477)
                ·
                  refine ⟨3009977041076911001574913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64212843542974101366931477 3009977041076911001574913)
                  ·
                    refine ⟨2257482780807683251181185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3009977041076911001574913 2257482780807683251181185)
                    ·
                      refine ⟨1693112085605762438385889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2257482780807683251181185 1693112085605762438385889)
                      ·
                        rfl

theorem cell23_3297324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 2, 2].length) (baseStart_3297324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297324 prefixEnd_3297324 := by exact prefixLift 3297324
  have htrace : WordTrace (prefixWord ++ tailWord_3297324) baseStart_3297324 baseEnd_3297324 := by
    simpa [prefixWord, tailWord_3297324, baseEnd_3297324] using wordTrace_append hprefix tailTrace_3297324
  have hstable : (prefixWord ++ tailWord_3297324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297324).length < 2 ^ (prefixWord ++ tailWord_3297324).sum := by decide
  have hdescent : baseEnd_3297324 < baseStart_3297324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297358 : List Nat := [4, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2]
def baseStart_3297358 : Nat := 118140960795 + 3297358 * 2 ^ 59
def prefixEnd_3297358 : Nat := 4983230072969 + 3 ^ 40 * 3297358 * 2
def baseEnd_3297358 : Nat := 1693129543948015305360733

theorem tailTrace_3297358 : CollatzResearch.WordTrace tailWord_3297358 prefixEnd_3297358 1693129543948015305360733 := by
  unfold tailWord_3297358
  simp only [CollatzResearch.WordTrace]
  refine ⟨15033065798530323094666591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80176350925495056504888485 15033065798530323094666591)
  ·
    refine ⟨22549598697795484641999887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15033065798530323094666591 22549598697795484641999887)
    ·
      refine ⟨33824398046693226962999831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22549598697795484641999887 33824398046693226962999831)
      ·
        refine ⟨50736597070039840444499747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33824398046693226962999831 50736597070039840444499747)
        ·
          refine ⟨76104895605059760666749621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50736597070039840444499747 76104895605059760666749621)
          ·
            refine ⟨7134833962974352562507777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76104895605059760666749621 7134833962974352562507777)
            ·
              refine ⟨5351125472230764421880833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7134833962974352562507777 5351125472230764421880833)
              ·
                refine ⟨4013344104173073316410625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5351125472230764421880833 4013344104173073316410625)
                ·
                  refine ⟨3010008078129804987307969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4013344104173073316410625 3010008078129804987307969)
                  ·
                    refine ⟨2257506058597353740480977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3010008078129804987307969 2257506058597353740480977)
                    ·
                      refine ⟨1693129543948015305360733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2257506058597353740480977 1693129543948015305360733)
                      ·
                        rfl

theorem cell23_3297358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_3297358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297358 prefixEnd_3297358 := by exact prefixLift 3297358
  have htrace : WordTrace (prefixWord ++ tailWord_3297358) baseStart_3297358 baseEnd_3297358 := by
    simpa [prefixWord, tailWord_3297358, baseEnd_3297358] using wordTrace_append hprefix tailTrace_3297358
  have hstable : (prefixWord ++ tailWord_3297358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297358).length < 2 ^ (prefixWord ++ tailWord_3297358).sum := by decide
  have hdescent : baseEnd_3297358 < baseStart_3297358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297360 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 5, 7]
def baseStart_3297360 : Nat := 118140960795 + 3297360 * 2 ^ 59
def prefixEnd_3297360 : Nat := 4983230072969 + 3 ^ 40 * 3297360 * 2
def baseEnd_3297360 : Nat := 564376856969774765845241

theorem tailTrace_3297360 : CollatzResearch.WordTrace tailWord_3297360 prefixEnd_3297360 564376856969774765845241 := by
  unfold tailWord_3297360
  simp only [CollatzResearch.WordTrace]
  refine ⟨60132299667117669549452767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80176399556156892732603689 60132299667117669549452767)
  ·
    refine ⟨90198449500676504324179151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60132299667117669549452767 90198449500676504324179151)
    ·
      refine ⟨135297674251014756486268727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90198449500676504324179151 135297674251014756486268727)
      ·
        refine ⟨202946511376522134729403091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135297674251014756486268727 202946511376522134729403091)
        ·
          refine ⟨304419767064783202094104637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202946511376522134729403091 304419767064783202094104637)
          ·
            refine ⟨114157412649293700785289239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304419767064783202094104637 114157412649293700785289239)
            ·
              refine ⟨171236118973940551177933859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114157412649293700785289239 171236118973940551177933859)
              ·
                refine ⟨256854178460910826766900789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171236118973940551177933859 256854178460910826766900789)
                ·
                  refine ⟨24080079230710390009396949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 256854178460910826766900789 24080079230710390009396949)
                  ·
                    refine ⟨564376856969774765845241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24080079230710390009396949 564376856969774765845241)
                    ·
                      rfl

theorem cell23_3297360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5, 7].length) (baseStart_3297360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297360 prefixEnd_3297360 := by exact prefixLift 3297360
  have htrace : WordTrace (prefixWord ++ tailWord_3297360) baseStart_3297360 baseEnd_3297360 := by
    simpa [prefixWord, tailWord_3297360, baseEnd_3297360] using wordTrace_append hprefix tailTrace_3297360
  have hstable : (prefixWord ++ tailWord_3297360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297360).length < 2 ^ (prefixWord ++ tailWord_3297360).sum := by decide
  have hdescent : baseEnd_3297360 < baseStart_3297360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297394 : List Nat := [3, 2, 1, 2, 2, 2, 3, 1, 2, 5]
def baseStart_3297394 : Nat := 118140960795 + 3297394 * 2 ^ 59
def prefixEnd_3297394 : Nat := 4983230072969 + 3 ^ 40 * 3297394 * 2
def baseEnd_3297394 : Nat := 564382676417192388170189

theorem tailTrace_3297394 : CollatzResearch.WordTrace tailWord_3297394 prefixEnd_3297394 564382676417192388170189 := by
  unfold tailWord_3297394
  simp only [CollatzResearch.WordTrace]
  refine ⟨30066459854028040726410809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80177226277408108603762157 30066459854028040726410809)
  ·
    refine ⟨22549844890521030544808107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30066459854028040726410809 22549844890521030544808107)
    ·
      refine ⟨33824767335781545817212161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22549844890521030544808107 33824767335781545817212161)
      ·
        refine ⟨25368575501836159362909121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33824767335781545817212161 25368575501836159362909121)
        ·
          refine ⟨19026431626377119522181841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25368575501836159362909121 19026431626377119522181841)
          ·
            refine ⟨14269823719782839641636381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19026431626377119522181841 14269823719782839641636381)
            ·
              refine ⟨5351183894918564865613643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14269823719782839641636381 5351183894918564865613643)
              ·
                refine ⟨8026775842377847298420465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5351183894918564865613643 8026775842377847298420465)
                ·
                  refine ⟨6020081881783385473815349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8026775842377847298420465 6020081881783385473815349)
                  ·
                    refine ⟨564382676417192388170189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6020081881783385473815349 564382676417192388170189)
                    ·
                      rfl

theorem cell23_3297394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_3297394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297394 prefixEnd_3297394 := by exact prefixLift 3297394
  have htrace : WordTrace (prefixWord ++ tailWord_3297394) baseStart_3297394 baseEnd_3297394 := by
    simpa [prefixWord, tailWord_3297394, baseEnd_3297394] using wordTrace_append hprefix tailTrace_3297394
  have hstable : (prefixWord ++ tailWord_3297394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297394).length < 2 ^ (prefixWord ++ tailWord_3297394).sum := by decide
  have hdescent : baseEnd_3297394 < baseStart_3297394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297424 : List Nat := [2, 1, 1, 1, 1, 1, 8, 1, 3, 4]
def baseStart_3297424 : Nat := 118140960795 + 3297424 * 2 ^ 59
def prefixEnd_3297424 : Nat := 4983230072969 + 3 ^ 40 * 3297424 * 2
def baseEnd_3297424 : Nat := 564387811223737349045143

theorem tailTrace_3297424 : CollatzResearch.WordTrace tailWord_3297424 prefixEnd_3297424 564387811223737349045143 := by
  unfold tailWord_3297424
  simp only [CollatzResearch.WordTrace]
  refine ⟨60133466803001739014617663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80177955737335652019490217 60133466803001739014617663)
  ·
    refine ⟨90200200204502608521926495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60133466803001739014617663 90200200204502608521926495)
    ·
      refine ⟨135300300306753912782889743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90200200204502608521926495 135300300306753912782889743)
      ·
        refine ⟨202950450460130869174334615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135300300306753912782889743 202950450460130869174334615)
        ·
          refine ⟨304425675690196303761501923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202950450460130869174334615 304425675690196303761501923)
          ·
            refine ⟨456638513535294455642252885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304425675690196303761501923 456638513535294455642252885)
            ·
              refine ⟨5351232580491731902057651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 456638513535294455642252885 5351232580491731902057651)
              ·
                refine ⟨8026848870737597853086477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5351232580491731902057651 8026848870737597853086477)
                ·
                  refine ⟨3010068326526599194907429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8026848870737597853086477 3010068326526599194907429)
                  ·
                    refine ⟨564387811223737349045143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3010068326526599194907429 564387811223737349045143)
                    ·
                      rfl

theorem cell23_3297424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 3, 4].length) (baseStart_3297424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297424 prefixEnd_3297424 := by exact prefixLift 3297424
  have htrace : WordTrace (prefixWord ++ tailWord_3297424) baseStart_3297424 baseEnd_3297424 := by
    simpa [prefixWord, tailWord_3297424, baseEnd_3297424] using wordTrace_append hprefix tailTrace_3297424
  have hstable : (prefixWord ++ tailWord_3297424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297424).length < 2 ^ (prefixWord ++ tailWord_3297424).sum := by decide
  have hdescent : baseEnd_3297424 < baseStart_3297424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297501 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 3, 5]
def baseStart_3297501 : Nat := 118140960795 + 3297501 * 2 ^ 59
def prefixEnd_3297501 : Nat := 4983230072969 + 3 ^ 40 * 3297501 * 2
def baseEnd_3297501 : Nat := 564400990560536081957525

theorem tailTrace_3297501 : CollatzResearch.WordTrace tailWord_3297501 prefixEnd_3297501 564400990560536081957525 := by
  unfold tailWord_3297501
  simp only [CollatzResearch.WordTrace]
  refine ⟨120269742026724520179788357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80179828017816346786525571 120269742026724520179788357)
  ·
    refine ⟨22550576630010847533710317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120269742026724520179788357 22550576630010847533710317)
    ·
      refine ⟨8456466236254067825141369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22550576630010847533710317 8456466236254067825141369)
      ·
        refine ⟨6342349677190550868856027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8456466236254067825141369 6342349677190550868856027)
        ·
          refine ⟨9513524515785826303284041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6342349677190550868856027 9513524515785826303284041)
          ·
            refine ⟨7135143386839369727463031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9513524515785826303284041 7135143386839369727463031)
            ·
              refine ⟨10702715080259054591194547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7135143386839369727463031 10702715080259054591194547)
              ·
                refine ⟨16054072620388581886791821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10702715080259054591194547 16054072620388581886791821)
                ·
                  refine ⟨6020277232645718207546933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16054072620388581886791821 6020277232645718207546933)
                  ·
                    refine ⟨564400990560536081957525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6020277232645718207546933 564400990560536081957525)
                    ·
                      rfl

theorem cell23_3297501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_3297501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297501 prefixEnd_3297501 := by exact prefixLift 3297501
  have htrace : WordTrace (prefixWord ++ tailWord_3297501) baseStart_3297501 baseEnd_3297501 := by
    simpa [prefixWord, tailWord_3297501, baseEnd_3297501] using wordTrace_append hprefix tailTrace_3297501
  have hstable : (prefixWord ++ tailWord_3297501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297501).length < 2 ^ (prefixWord ++ tailWord_3297501).sum := by decide
  have hdescent : baseEnd_3297501 < baseStart_3297501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297504 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 4]
def baseStart_3297504 : Nat := 118140960795 + 3297504 * 2 ^ 59
def prefixEnd_3297504 : Nat := 4983230072969 + 3 ^ 40 * 3297504 * 2
def baseEnd_3297504 : Nat := 1693204512123571734135061

theorem tailTrace_3297504 : CollatzResearch.WordTrace tailWord_3297504 prefixEnd_3297504 1693204512123571734135061 := by
  unfold tailWord_3297504
  simp only [CollatzResearch.WordTrace]
  refine ⟨60134925722856825846073783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80179900963809101128098377 60134925722856825846073783)
  ·
    refine ⟨90202388584285238769110675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60134925722856825846073783 90202388584285238769110675)
    ·
      refine ⟨135303582876427858153666013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90202388584285238769110675 135303582876427858153666013)
      ·
        refine ⟨50738843578660446807624755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135303582876427858153666013 50738843578660446807624755)
        ·
          refine ⟨76108265367990670211437133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50738843578660446807624755 76108265367990670211437133)
          ·
            refine ⟨28540599512996501329288925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76108265367990670211437133 28540599512996501329288925)
            ·
              refine ⟨10702724817373687998483347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28540599512996501329288925 10702724817373687998483347)
              ·
                refine ⟨16054087226060531997725021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10702724817373687998483347 16054087226060531997725021)
                ·
                  refine ⟨6020282709772699499146883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16054087226060531997725021 6020282709772699499146883)
                  ·
                    refine ⟨9030424064659049248720325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6020282709772699499146883 9030424064659049248720325)
                    ·
                      refine ⟨1693204512123571734135061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9030424064659049248720325 1693204512123571734135061)
                      ·
                        rfl

theorem cell23_3297504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_3297504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297504 prefixEnd_3297504 := by exact prefixLift 3297504
  have htrace : WordTrace (prefixWord ++ tailWord_3297504) baseStart_3297504 baseEnd_3297504 := by
    simpa [prefixWord, tailWord_3297504, baseEnd_3297504] using wordTrace_append hprefix tailTrace_3297504
  have hstable : (prefixWord ++ tailWord_3297504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297504).length < 2 ^ (prefixWord ++ tailWord_3297504).sum := by decide
  have hdescent : baseEnd_3297504 < baseStart_3297504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297514 : List Nat := [3, 1, 3, 1, 1, 2, 3, 2, 1, 6]
def baseStart_3297514 : Nat := 118140960795 + 3297514 * 2 ^ 59
def prefixEnd_3297514 : Nat := 4983230072969 + 3 ^ 40 * 3297514 * 2
def baseEnd_3297514 : Nat := 564403215643372231670005

theorem tailTrace_3297514 : CollatzResearch.WordTrace tailWord_3297514 prefixEnd_3297514 564403215643372231670005 := by
  unfold tailWord_3297514
  simp only [CollatzResearch.WordTrace]
  refine ⟨30067554043919355850002899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80180144117118282266674397 30067554043919355850002899)
  ·
    refine ⟨45101331065879033775004349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30067554043919355850002899 45101331065879033775004349)
    ·
      refine ⟨16912999149704637665626631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45101331065879033775004349 16912999149704637665626631)
      ·
        refine ⟨25369498724556956498439947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16912999149704637665626631 25369498724556956498439947)
        ·
          refine ⟨38054248086835434747659921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25369498724556956498439947 38054248086835434747659921)
          ·
            refine ⟨28540686065126576060744941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38054248086835434747659921 28540686065126576060744941)
            ·
              refine ⟨10702757274422466022779353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28540686065126576060744941 10702757274422466022779353)
              ·
                refine ⟨8027067955816849517084515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10702757274422466022779353 8027067955816849517084515)
                ·
                  refine ⟨12040601933725274275626773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8027067955816849517084515 12040601933725274275626773)
                  ·
                    refine ⟨564403215643372231670005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12040601933725274275626773 564403215643372231670005)
                    ·
                      rfl

theorem cell23_3297514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_3297514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297514 prefixEnd_3297514 := by exact prefixLift 3297514
  have htrace : WordTrace (prefixWord ++ tailWord_3297514) baseStart_3297514 baseEnd_3297514 := by
    simpa [prefixWord, tailWord_3297514, baseEnd_3297514] using wordTrace_append hprefix tailTrace_3297514
  have hstable : (prefixWord ++ tailWord_3297514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297514).length < 2 ^ (prefixWord ++ tailWord_3297514).sum := by decide
  have hdescent : baseEnd_3297514 < baseStart_3297514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297532 : List Nat := [2, 2, 2, 1, 4, 3, 2, 2, 1, 1, 3]
def baseStart_3297532 : Nat := 118140960795 + 3297532 * 2 ^ 59
def prefixEnd_3297532 : Nat := 4983230072969 + 3 ^ 40 * 3297532 * 2
def baseEnd_3297532 : Nat := 1693218889581897624584933

theorem tailTrace_3297532 : CollatzResearch.WordTrace tailWord_3297532 prefixEnd_3297532 1693218889581897624584933 := by
  unfold tailWord_3297532
  simp only [CollatzResearch.WordTrace]
  refine ⟨60135436344806106237083425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80180581793074808316111233 60135436344806106237083425)
  ·
    refine ⟨45101577258604579677812569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60135436344806106237083425 45101577258604579677812569)
    ·
      refine ⟨33826182943953434758359427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45101577258604579677812569 33826182943953434758359427)
      ·
        refine ⟨50739274415930152137539141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33826182943953434758359427 50739274415930152137539141)
        ·
          refine ⟨9513613952986903525788589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50739274415930152137539141 9513613952986903525788589)
          ·
            refine ⟨3567605232370088822170721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9513613952986903525788589 3567605232370088822170721)
            ·
              refine ⟨2675703924277566616628041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3567605232370088822170721 2675703924277566616628041)
              ·
                refine ⟨2006777943208174962471031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2675703924277566616628041 2006777943208174962471031)
                ·
                  refine ⟨3010166914812262443706547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2006777943208174962471031 3010166914812262443706547)
                  ·
                    refine ⟨4515250372218393665559821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3010166914812262443706547 4515250372218393665559821)
                    ·
                      refine ⟨1693218889581897624584933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4515250372218393665559821 1693218889581897624584933)
                      ·
                        rfl

theorem cell23_3297532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_3297532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297532 prefixEnd_3297532 := by exact prefixLift 3297532
  have htrace : WordTrace (prefixWord ++ tailWord_3297532) baseStart_3297532 baseEnd_3297532 := by
    simpa [prefixWord, tailWord_3297532, baseEnd_3297532] using wordTrace_append hprefix tailTrace_3297532
  have hstable : (prefixWord ++ tailWord_3297532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297532).length < 2 ^ (prefixWord ++ tailWord_3297532).sum := by decide
  have hdescent : baseEnd_3297532 < baseStart_3297532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297544 : List Nat := [2, 1, 3, 2, 3, 1, 3, 8]
def baseStart_3297544 : Nat := 118140960795 + 3297544 * 2 ^ 59
def prefixEnd_3297544 : Nat := 4983230072969 + 3 ^ 40 * 3297544 * 2
def baseEnd_3297544 : Nat := 62712038938879688060551

theorem tailTrace_3297544 : CollatzResearch.WordTrace tailWord_3297544 prefixEnd_3297544 62712038938879688060551 := by
  unfold tailWord_3297544
  simp only [CollatzResearch.WordTrace]
  refine ⟨60135655182784369261801843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80180873577045825682402457 60135655182784369261801843)
  ·
    refine ⟨90203482774176553892702765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60135655182784369261801843 90203482774176553892702765)
    ·
      refine ⟨33826306040316207709763537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90203482774176553892702765 33826306040316207709763537)
      ·
        refine ⟨25369729530237155782322653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33826306040316207709763537 25369729530237155782322653)
        ·
          refine ⟨9513648573838933418370995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25369729530237155782322653 9513648573838933418370995)
          ·
            refine ⟨14270472860758400127556493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9513648573838933418370995 14270472860758400127556493)
            ·
              refine ⟨5351427322784400047833685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14270472860758400127556493 5351427322784400047833685)
              ·
                refine ⟨62712038938879688060551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5351427322784400047833685 62712038938879688060551)
                ·
                  rfl

theorem cell23_3297544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 8].length) (baseStart_3297544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297544 prefixEnd_3297544 := by exact prefixLift 3297544
  have htrace : WordTrace (prefixWord ++ tailWord_3297544) baseStart_3297544 baseEnd_3297544 := by
    simpa [prefixWord, tailWord_3297544, baseEnd_3297544] using wordTrace_append hprefix tailTrace_3297544
  have hstable : (prefixWord ++ tailWord_3297544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297544).length < 2 ^ (prefixWord ++ tailWord_3297544).sum := by decide
  have hdescent : baseEnd_3297544 < baseStart_3297544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297571 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 4, 1, 3]
def baseStart_3297571 : Nat := 118140960795 + 3297571 * 2 ^ 59
def prefixEnd_3297571 : Nat := 4983230072969 + 3 ^ 40 * 3297571 * 2
def baseEnd_3297571 : Nat := 1693238915327422971997253

theorem tailTrace_3297571 : CollatzResearch.WordTrace tailWord_3297571 prefixEnd_3297571 1693238915327422971997253 := by
  unfold tailWord_3297571
  simp only [CollatzResearch.WordTrace]
  refine ⟨120272295136470922134836567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80181530090980614756557711 120272295136470922134836567)
  ·
    refine ⟨180408442704706383202254851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120272295136470922134836567 180408442704706383202254851)
    ·
      refine ⟨270612664057059574803382277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180408442704706383202254851 270612664057059574803382277)
      ·
        refine ⟨50739874510698670275634177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270612664057059574803382277 50739874510698670275634177)
        ·
          refine ⟨38054905883024002706725633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50739874510698670275634177 38054905883024002706725633)
          ·
            refine ⟨28541179412268002030044225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38054905883024002706725633 28541179412268002030044225)
            ·
              refine ⟨21405884559201001522533169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28541179412268002030044225 21405884559201001522533169)
              ·
                refine ⟨16054413419400751141899877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21405884559201001522533169 16054413419400751141899877)
                ·
                  refine ⟨3010202516137640839106227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16054413419400751141899877 3010202516137640839106227)
                  ·
                    refine ⟨4515303774206461258659341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3010202516137640839106227 4515303774206461258659341)
                    ·
                      refine ⟨1693238915327422971997253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4515303774206461258659341 1693238915327422971997253)
                      ·
                        rfl

theorem cell23_3297571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_3297571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297571 prefixEnd_3297571 := by exact prefixLift 3297571
  have htrace : WordTrace (prefixWord ++ tailWord_3297571) baseStart_3297571 baseEnd_3297571 := by
    simpa [prefixWord, tailWord_3297571, baseEnd_3297571] using wordTrace_append hprefix tailTrace_3297571
  have hstable : (prefixWord ++ tailWord_3297571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297571).length < 2 ^ (prefixWord ++ tailWord_3297571).sum := by decide
  have hdescent : baseEnd_3297571 < baseStart_3297571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297572 : List Nat := [2, 3, 1, 3, 1, 3, 2, 3, 1, 2, 2]
def baseStart_3297572 : Nat := 118140960795 + 3297572 * 2 ^ 59
def prefixEnd_3297572 : Nat := 4983230072969 + 3 ^ 40 * 3297572 * 2
def baseEnd_3297572 : Nat := 1693239428808077468084749

theorem tailTrace_3297572 : CollatzResearch.WordTrace tailWord_3297572 prefixEnd_3297572 1693239428808077468084749 := by
  unfold tailWord_3297572
  simp only [CollatzResearch.WordTrace]
  refine ⟨60136165804733649652811485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80181554406311532870415313 60136165804733649652811485)
  ·
    refine ⟨22551062176775118619804307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60136165804733649652811485 22551062176775118619804307)
    ·
      refine ⟨33826593265162677929706461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22551062176775118619804307 33826593265162677929706461)
      ·
        refine ⟨12684972474436004223639923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33826593265162677929706461 12684972474436004223639923)
        ·
          refine ⟨19027458711654006335459885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12684972474436004223639923 19027458711654006335459885)
          ·
            refine ⟨7135297016870252375797457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19027458711654006335459885 7135297016870252375797457)
            ·
              refine ⟨5351472762652689281848093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7135297016870252375797457 5351472762652689281848093)
              ·
                refine ⟨2006802285994758480693035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5351472762652689281848093 2006802285994758480693035)
                ·
                  refine ⟨3010203428992137721039553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2006802285994758480693035 3010203428992137721039553)
                  ·
                    refine ⟨2257652571744103290779665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3010203428992137721039553 2257652571744103290779665)
                    ·
                      refine ⟨1693239428808077468084749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2257652571744103290779665 1693239428808077468084749)
                      ·
                        rfl

theorem cell23_3297572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_3297572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297572 prefixEnd_3297572 := by exact prefixLift 3297572
  have htrace : WordTrace (prefixWord ++ tailWord_3297572) baseStart_3297572 baseEnd_3297572 := by
    simpa [prefixWord, tailWord_3297572, baseEnd_3297572] using wordTrace_append hprefix tailTrace_3297572
  have hstable : (prefixWord ++ tailWord_3297572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297572).length < 2 ^ (prefixWord ++ tailWord_3297572).sum := by decide
  have hdescent : baseEnd_3297572 < baseStart_3297572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297582 : List Nat := [4, 1, 3, 3, 1, 2, 1, 2, 2, 4]
def baseStart_3297582 : Nat := 118140960795 + 3297582 * 2 ^ 59
def prefixEnd_3297582 : Nat := 4983230072969 + 3 ^ 40 * 3297582 * 2
def baseEnd_3297582 : Nat := 564414854538207476319901

theorem tailTrace_3297582 : CollatzResearch.WordTrace tailWord_3297582 prefixEnd_3297582 564414854538207476319901 := by
  unfold tailWord_3297582
  simp only [CollatzResearch.WordTrace]
  refine ⟨15034087042428883876685875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80181797559620714008991333 15034087042428883876685875)
  ·
    refine ⟨22551130563643325815028813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15034087042428883876685875 22551130563643325815028813)
    ·
      refine ⟨8456673961366247180635805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22551130563643325815028813 8456673961366247180635805)
      ·
        refine ⟨3171252735512342692738427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8456673961366247180635805 3171252735512342692738427)
        ·
          refine ⟨4756879103268514039107641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3171252735512342692738427 4756879103268514039107641)
          ·
            refine ⟨3567659327451385529330731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4756879103268514039107641 3567659327451385529330731)
            ·
              refine ⟨5351488991177078293996097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3567659327451385529330731 5351488991177078293996097)
              ·
                refine ⟨4013616743382808720497073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5351488991177078293996097 4013616743382808720497073)
                ·
                  refine ⟨3010212557537106540372805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4013616743382808720497073 3010212557537106540372805)
                  ·
                    refine ⟨564414854538207476319901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3010212557537106540372805 564414854538207476319901)
                    ·
                      rfl

theorem cell23_3297582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_3297582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297582 prefixEnd_3297582 := by exact prefixLift 3297582
  have htrace : WordTrace (prefixWord ++ tailWord_3297582) baseStart_3297582 baseEnd_3297582 := by
    simpa [prefixWord, tailWord_3297582, baseEnd_3297582] using wordTrace_append hprefix tailTrace_3297582
  have hstable : (prefixWord ++ tailWord_3297582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297582).length < 2 ^ (prefixWord ++ tailWord_3297582).sum := by decide
  have hdescent : baseEnd_3297582 < baseStart_3297582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297611 : List Nat := [1, 1, 1, 1, 3, 1, 1, 7, 1, 4, 2]
def baseStart_3297611 : Nat := 118140960795 + 3297611 * 2 ^ 59
def prefixEnd_3297611 : Nat := 4983230072969 + 3 ^ 40 * 3297611 * 2
def baseEnd_3297611 : Nat := 1693259454553602815497069

theorem tailTrace_3297611 : CollatzResearch.WordTrace tailWord_3297611 prefixEnd_3297611 1693259454553602815497069 := by
  unfold tailWord_3297611
  simp only [CollatzResearch.WordTrace]
  refine ⟨120273754056326008966292687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80182502704217339310861791 120273754056326008966292687)
  ·
    refine ⟨180410631084489013449439031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120273754056326008966292687 180410631084489013449439031)
    ·
      refine ⟨270615946626733520174158547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180410631084489013449439031 270615946626733520174158547)
      ·
        refine ⟨405923919940100280261237821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270615946626733520174158547 405923919940100280261237821)
        ·
          refine ⟨152221469977537605097964183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405923919940100280261237821 152221469977537605097964183)
          ·
            refine ⟨228332204966306407646946275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152221469977537605097964183 228332204966306407646946275)
            ·
              refine ⟨342498307449459611470419413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228332204966306407646946275 342498307449459611470419413)
              ·
                refine ⟨8027304080846709643837955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 342498307449459611470419413 8027304080846709643837955)
                ·
                  refine ⟨12040956121270064465756933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8027304080846709643837955 12040956121270064465756933)
                  ·
                    refine ⟨2257679272738137087329425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12040956121270064465756933 2257679272738137087329425)
                    ·
                      refine ⟨1693259454553602815497069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2257679272738137087329425 1693259454553602815497069)
                      ·
                        rfl

theorem cell23_3297611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 4, 2].length) (baseStart_3297611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297611 prefixEnd_3297611 := by exact prefixLift 3297611
  have htrace : WordTrace (prefixWord ++ tailWord_3297611) baseStart_3297611 baseEnd_3297611 := by
    simpa [prefixWord, tailWord_3297611, baseEnd_3297611] using wordTrace_append hprefix tailTrace_3297611
  have hstable : (prefixWord ++ tailWord_3297611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297611).length < 2 ^ (prefixWord ++ tailWord_3297611).sum := by decide
  have hdescent : baseEnd_3297611 < baseStart_3297611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297624 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 4, 2, 4]
def baseStart_3297624 : Nat := 118140960795 + 3297624 * 2 ^ 59
def prefixEnd_3297624 : Nat := 4983230072969 + 3 ^ 40 * 3297624 * 2
def baseEnd_3297624 : Nat := 1693266129802111264634509

theorem tailTrace_3297624 : CollatzResearch.WordTrace tailWord_3297624 prefixEnd_3297624 1693266129802111264634509 := by
  unfold tailWord_3297624
  simp only [CollatzResearch.WordTrace]
  refine ⟨60137114102639456093257963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80182818803519274791010617 60137114102639456093257963)
  ·
    refine ⟨90205671153959184139886945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60137114102639456093257963 90205671153959184139886945)
    ·
      refine ⟨67654253365469388104915209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90205671153959184139886945 67654253365469388104915209)
      ·
        refine ⟨50740690024102041078686407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67654253365469388104915209 50740690024102041078686407)
        ·
          refine ⟨76111035036153061618029611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50740690024102041078686407 76111035036153061618029611)
          ·
            refine ⟨114166552554229592427044417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76111035036153061618029611 114166552554229592427044417)
            ·
              refine ⟨85624914415672194320283313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114166552554229592427044417 85624914415672194320283313)
              ·
                refine ⟨64218685811754145740212485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85624914415672194320283313 64218685811754145740212485)
                ·
                  refine ⟨12041003589703902326289841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64218685811754145740212485 12041003589703902326289841)
                  ·
                    refine ⟨9030752692277926744717381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12041003589703902326289841 9030752692277926744717381)
                    ·
                      refine ⟨1693266129802111264634509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9030752692277926744717381 1693266129802111264634509)
                      ·
                        rfl

theorem cell23_3297624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_3297624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297624 prefixEnd_3297624 := by exact prefixLift 3297624
  have htrace : WordTrace (prefixWord ++ tailWord_3297624) baseStart_3297624 baseEnd_3297624 := by
    simpa [prefixWord, tailWord_3297624, baseEnd_3297624] using wordTrace_append hprefix tailTrace_3297624
  have hstable : (prefixWord ++ tailWord_3297624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297624).length < 2 ^ (prefixWord ++ tailWord_3297624).sum := by decide
  have hdescent : baseEnd_3297624 < baseStart_3297624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297645 : List Nat := [1, 5, 1, 1, 1, 2, 2, 4, 2, 2, 2]
def baseStart_3297645 : Nat := 118140960795 + 3297645 * 2 ^ 59
def prefixEnd_3297645 : Nat := 4983230072969 + 3 ^ 40 * 3297645 * 2
def baseEnd_3297645 : Nat := 1693276912895855682471913

theorem tailTrace_3297645 : CollatzResearch.WordTrace tailWord_3297645 prefixEnd_3297645 1693276912895855682471913 := by
  unfold tailWord_3297645
  simp only [CollatzResearch.WordTrace]
  refine ⟨120274994138202832773030389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80183329425468555182020259 120274994138202832773030389)
  ·
    refine ⟨11275780700456515572471599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120274994138202832773030389 11275780700456515572471599)
    ·
      refine ⟨16913671050684773358707399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11275780700456515572471599 16913671050684773358707399)
      ·
        refine ⟨25370506576027160038061099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16913671050684773358707399 25370506576027160038061099)
        ·
          refine ⟨38055759864040740057091649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25370506576027160038061099 38055759864040740057091649)
          ·
            refine ⟨28541819898030555042818737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38055759864040740057091649 28541819898030555042818737)
            ·
              refine ⟨21406364923522916282114053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28541819898030555042818737 21406364923522916282114053)
              ·
                refine ⟨4013693423160546802896385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21406364923522916282114053 4013693423160546802896385)
                ·
                  refine ⟨3010270067370410102172289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4013693423160546802896385 3010270067370410102172289)
                  ·
                    refine ⟨2257702550527807576629217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3010270067370410102172289 2257702550527807576629217)
                    ·
                      refine ⟨1693276912895855682471913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2257702550527807576629217 1693276912895855682471913)
                      ·
                        rfl

theorem cell23_3297645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_3297645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297645 prefixEnd_3297645 := by exact prefixLift 3297645
  have htrace : WordTrace (prefixWord ++ tailWord_3297645) baseStart_3297645 baseEnd_3297645 := by
    simpa [prefixWord, tailWord_3297645, baseEnd_3297645] using wordTrace_append hprefix tailTrace_3297645
  have hstable : (prefixWord ++ tailWord_3297645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297645).length < 2 ^ (prefixWord ++ tailWord_3297645).sum := by decide
  have hdescent : baseEnd_3297645 < baseStart_3297645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297666 : List Nat := [3, 4, 2, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_3297666 : Nat := 118140960795 + 3297666 * 2 ^ 59
def prefixEnd_3297666 : Nat := 4983230072969 + 3 ^ 40 * 3297666 * 2
def baseEnd_3297666 : Nat := 1693287695989600100309317

theorem tailTrace_3297666 : CollatzResearch.WordTrace tailWord_3297666 prefixEnd_3297666 1693287695989600100309317 := by
  unfold tailWord_3297666
  simp only [CollatzResearch.WordTrace]
  refine ⟨30068940017781688339886213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80183840047417835573029901 30068940017781688339886213)
  ·
    refine ⟨5637926253334066563728665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30068940017781688339886213 5637926253334066563728665)
    ·
      refine ⟨4228444690000549922796499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5637926253334066563728665 4228444690000549922796499)
      ·
        refine ⟨6342667035000824884194749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4228444690000549922796499 6342667035000824884194749)
        ·
          refine ⟨2378500138125309331573031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6342667035000824884194749 2378500138125309331573031)
          ·
            refine ⟨3567750207187963997359547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378500138125309331573031 3567750207187963997359547)
            ·
              refine ⟨5351625310781945996039321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3567750207187963997359547 5351625310781945996039321)
              ·
                refine ⟨4013718983086459497029491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5351625310781945996039321 4013718983086459497029491)
                ·
                  refine ⟨6020578474629689245544237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4013718983086459497029491 6020578474629689245544237)
                  ·
                    refine ⟨2257716927986133467079089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6020578474629689245544237 2257716927986133467079089)
                    ·
                      refine ⟨1693287695989600100309317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2257716927986133467079089 1693287695989600100309317)
                      ·
                        rfl

theorem cell23_3297666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_3297666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297666 prefixEnd_3297666 := by exact prefixLift 3297666
  have htrace : WordTrace (prefixWord ++ tailWord_3297666) baseStart_3297666 baseEnd_3297666 := by
    simpa [prefixWord, tailWord_3297666, baseEnd_3297666] using wordTrace_append hprefix tailTrace_3297666
  have hstable : (prefixWord ++ tailWord_3297666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297666).length < 2 ^ (prefixWord ++ tailWord_3297666).sum := by decide
  have hdescent : baseEnd_3297666 < baseStart_3297666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297701 : List Nat := [1, 3, 1, 2, 1, 1, 3, 4, 2, 1, 4]
def baseStart_3297701 : Nat := 118140960795 + 3297701 * 2 ^ 59
def prefixEnd_3297701 : Nat := 4983230072969 + 3 ^ 40 * 3297701 * 2
def baseEnd_3297701 : Nat := 1693305667812507463371655

theorem tailTrace_3297701 : CollatzResearch.WordTrace tailWord_3297701 prefixEnd_3297701 1693305667812507463371655 := by
  unfold tailWord_3297701
  simp only [CollatzResearch.WordTrace]
  refine ⟨120277036625999954337068957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80184691083999969558045971 120277036625999954337068957)
  ·
    refine ⟨45103888734749982876400859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120277036625999954337068957 45103888734749982876400859)
    ·
      refine ⟨67655833102124974314601289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45103888734749982876400859 67655833102124974314601289)
      ·
        refine ⟨50741874826593730735950967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67655833102124974314601289 50741874826593730735950967)
        ·
          refine ⟨76112812239890596103926451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50741874826593730735950967 76112812239890596103926451)
          ·
            refine ⟨114169218359835894155889677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76112812239890596103926451 114169218359835894155889677)
            ·
              refine ⟨42813456884938460308458629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114169218359835894155889677 42813456884938460308458629)
              ·
                refine ⟨8027523165925961307835993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42813456884938460308458629 8027523165925961307835993)
                ·
                  refine ⟨6020642374444470980876995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8027523165925961307835993 6020642374444470980876995)
                  ·
                    refine ⟨9030963561666706471315493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6020642374444470980876995 9030963561666706471315493)
                    ·
                      refine ⟨1693305667812507463371655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9030963561666706471315493 1693305667812507463371655)
                      ·
                        rfl

theorem cell23_3297701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_3297701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297701 prefixEnd_3297701 := by exact prefixLift 3297701
  have htrace : WordTrace (prefixWord ++ tailWord_3297701) baseStart_3297701 baseEnd_3297701 := by
    simpa [prefixWord, tailWord_3297701, baseEnd_3297701] using wordTrace_append hprefix tailTrace_3297701
  have hstable : (prefixWord ++ tailWord_3297701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297701).length < 2 ^ (prefixWord ++ tailWord_3297701).sum := by decide
  have hdescent : baseEnd_3297701 < baseStart_3297701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297732 : List Nat := [2, 3, 3, 2, 3, 1, 1, 1, 2, 5]
def baseStart_3297732 : Nat := 118140960795 + 3297732 * 2 ^ 59
def prefixEnd_3297732 : Nat := 4983230072969 + 3 ^ 40 * 3297732 * 2
def baseEnd_3297732 : Nat := 564440528570932280694671

theorem tailTrace_3297732 : CollatzResearch.WordTrace tailWord_3297732 prefixEnd_3297732 564440528570932280694671 := by
  unfold tailWord_3297732
  simp only [CollatzResearch.WordTrace]
  refine ⟨60139083644443823315723725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80185444859258431087631633 60139083644443823315723725)
  ·
    refine ⟨22552156366666433743396397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60139083644443823315723725 22552156366666433743396397)
    ·
      refine ⟨8457058637499912653773649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22552156366666433743396397 8457058637499912653773649)
      ·
        refine ⟨6342793978124934490330237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8457058637499912653773649 6342793978124934490330237)
        ·
          refine ⟨2378547741796850433873839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6342793978124934490330237 2378547741796850433873839)
          ·
            refine ⟨3567821612695275650810759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378547741796850433873839 3567821612695275650810759)
            ·
              refine ⟨5351732419042913476216139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3567821612695275650810759 5351732419042913476216139)
              ·
                refine ⟨8027598628564370214324209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5351732419042913476216139 8027598628564370214324209)
                ·
                  refine ⟨6020698971423277660743157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8027598628564370214324209 6020698971423277660743157)
                  ·
                    refine ⟨564440528570932280694671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6020698971423277660743157 564440528570932280694671)
                    ·
                      rfl

theorem cell23_3297732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_3297732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297732 prefixEnd_3297732 := by exact prefixLift 3297732
  have htrace : WordTrace (prefixWord ++ tailWord_3297732) baseStart_3297732 baseEnd_3297732 := by
    simpa [prefixWord, tailWord_3297732, baseEnd_3297732] using wordTrace_append hprefix tailTrace_3297732
  have hstable : (prefixWord ++ tailWord_3297732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297732).length < 2 ^ (prefixWord ++ tailWord_3297732).sum := by decide
  have hdescent : baseEnd_3297732 < baseStart_3297732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297744 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 8]
def baseStart_3297744 : Nat := 118140960795 + 3297744 * 2 ^ 59
def prefixEnd_3297744 : Nat := 4983230072969 + 3 ^ 40 * 3297744 * 2
def baseEnd_3297744 : Nat := 1693327747480650795133957

theorem tailTrace_3297744 : CollatzResearch.WordTrace tailWord_3297744 prefixEnd_3297744 1693327747480650795133957 := by
  unfold tailWord_3297744
  simp only [CollatzResearch.WordTrace]
  refine ⟨60139302482422086340442143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80185736643229448453922857 60139302482422086340442143)
  ·
    refine ⟨90208953723633129510663215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60139302482422086340442143 90208953723633129510663215)
    ·
      refine ⟨135313430585449694265994823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90208953723633129510663215 135313430585449694265994823)
      ·
        refine ⟨202970145878174541398992235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135313430585449694265994823 202970145878174541398992235)
        ·
          refine ⟨304455218817261812098488353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202970145878174541398992235 304455218817261812098488353)
          ·
            refine ⟨228341414112946359073866265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304455218817261812098488353 228341414112946359073866265)
            ·
              refine ⟨171256060584709769305399699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228341414112946359073866265 171256060584709769305399699)
              ·
                refine ⟨256884090877064653958099549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171256060584709769305399699 256884090877064653958099549)
                ·
                  refine ⟨96331534078899245234287331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256884090877064653958099549 96331534078899245234287331)
                  ·
                    refine ⟨144497301118348867851430997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96331534078899245234287331 144497301118348867851430997)
                    ·
                      refine ⟨1693327747480650795133957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 144497301118348867851430997 1693327747480650795133957)
                      ·
                        rfl

theorem cell23_3297744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_3297744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297744 prefixEnd_3297744 := by exact prefixLift 3297744
  have htrace : WordTrace (prefixWord ++ tailWord_3297744) baseStart_3297744 baseEnd_3297744 := by
    simpa [prefixWord, tailWord_3297744, baseEnd_3297744] using wordTrace_append hprefix tailTrace_3297744
  have hstable : (prefixWord ++ tailWord_3297744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297744).length < 2 ^ (prefixWord ++ tailWord_3297744).sum := by decide
  have hdescent : baseEnd_3297744 < baseStart_3297744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297812 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_3297812 : Nat := 118140960795 + 3297812 * 2 ^ 59
def prefixEnd_3297812 : Nat := 4983230072969 + 3 ^ 40 * 3297812 * 2
def baseEnd_3297812 : Nat := 1693362664165156529083645

theorem tailTrace_3297812 : CollatzResearch.WordTrace tailWord_3297812 prefixEnd_3297812 1693362664165156529083645 := by
  unfold tailWord_3297812
  simp only [CollatzResearch.WordTrace]
  refine ⟨60140542564298910147179845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80187390085731880196239793 60140542564298910147179845)
  ·
    refine ⟨11276351730806045652596221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60140542564298910147179845 11276351730806045652596221)
    ·
      refine ⟨4228631899052267119723583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11276351730806045652596221 4228631899052267119723583)
      ·
        refine ⟨6342947848578400679585375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4228631899052267119723583 6342947848578400679585375)
        ·
          refine ⟨9514421772867601019378063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6342947848578400679585375 9514421772867601019378063)
          ·
            refine ⟨14271632659301401529067095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9514421772867601019378063 14271632659301401529067095)
            ·
              refine ⟨21407448988952102293600643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14271632659301401529067095 21407448988952102293600643)
              ·
                refine ⟨32111173483428153440400965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21407448988952102293600643 32111173483428153440400965)
                ·
                  refine ⟨6020845028142778770075181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32111173483428153440400965 6020845028142778770075181)
                  ·
                    refine ⟨2257816885553542038778193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6020845028142778770075181 2257816885553542038778193)
                    ·
                      refine ⟨1693362664165156529083645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2257816885553542038778193 1693362664165156529083645)
                      ·
                        rfl

theorem cell23_3297812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_3297812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297812 prefixEnd_3297812 := by exact prefixLift 3297812
  have htrace : WordTrace (prefixWord ++ tailWord_3297812) baseStart_3297812 baseEnd_3297812 := by
    simpa [prefixWord, tailWord_3297812, baseEnd_3297812] using wordTrace_append hprefix tailTrace_3297812
  have hstable : (prefixWord ++ tailWord_3297812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297812).length < 2 ^ (prefixWord ++ tailWord_3297812).sum := by decide
  have hdescent : baseEnd_3297812 < baseStart_3297812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297818 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 4, 4]
def baseStart_3297818 : Nat := 118140960795 + 3297818 * 2 ^ 59
def prefixEnd_3297818 : Nat := 4983230072969 + 3 ^ 40 * 3297818 * 2
def baseEnd_3297818 : Nat := 564455248349694501869539

theorem tailTrace_3297818 : CollatzResearch.WordTrace tailWord_3297818 prefixEnd_3297818 564455248349694501869539 := by
  unfold tailWord_3297818
  simp only [CollatzResearch.WordTrace]
  refine ⟨30070325991644020829769527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80187535977717388879385405 30070325991644020829769527)
  ·
    refine ⟨45105488987466031244654291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30070325991644020829769527 45105488987466031244654291)
    ·
      refine ⟨67658233481199046866981437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45105488987466031244654291 67658233481199046866981437)
      ·
        refine ⟨25371837555449642575118039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67658233481199046866981437 25371837555449642575118039)
        ·
          refine ⟨38057756333174463862677059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25371837555449642575118039 38057756333174463862677059)
          ·
            refine ⟨57086634499761695794015589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38057756333174463862677059 57086634499761695794015589)
            ·
              refine ⟨10703743968705317961377923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57086634499761695794015589 10703743968705317961377923)
              ·
                refine ⟨16055615953057976942066885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10703743968705317961377923 16055615953057976942066885)
                ·
                  refine ⟨3010427991198370676637541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16055615953057976942066885 3010427991198370676637541)
                  ·
                    refine ⟨564455248349694501869539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3010427991198370676637541 564455248349694501869539)
                    ·
                      rfl

theorem cell23_3297818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_3297818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297818 prefixEnd_3297818 := by exact prefixLift 3297818
  have htrace : WordTrace (prefixWord ++ tailWord_3297818) baseStart_3297818 baseEnd_3297818 := by
    simpa [prefixWord, tailWord_3297818, baseEnd_3297818] using wordTrace_append hprefix tailTrace_3297818
  have hstable : (prefixWord ++ tailWord_3297818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297818).length < 2 ^ (prefixWord ++ tailWord_3297818).sum := by decide
  have hdescent : baseEnd_3297818 < baseStart_3297818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297862 : List Nat := [6, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_3297862 : Nat := 118140960795 + 3297862 * 2 ^ 59
def prefixEnd_3297862 : Nat := 4983230072969 + 3 ^ 40 * 3297862 * 2
def baseEnd_3297862 : Nat := 1693388338197881333458415

theorem tailTrace_3297862 : CollatzResearch.WordTrace tailWord_3297862 prefixEnd_3297862 1693388338197881333458415 := by
  unfold tailWord_3297862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3758840899325521213552495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80188605852277785889119893 3758840899325521213552495)
  ·
    refine ⟨5638261348988281820328743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3758840899325521213552495 5638261348988281820328743)
    ·
      refine ⟨8457392023482422730493115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5638261348988281820328743 8457392023482422730493115)
      ·
        refine ⟨12686088035223634095739673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8457392023482422730493115 12686088035223634095739673)
        ·
          refine ⟨9514566026417725571804755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12686088035223634095739673 9514566026417725571804755)
          ·
            refine ⟨14271849039626588357707133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9514566026417725571804755 14271849039626588357707133)
            ·
              refine ⟨5351943389859970634140175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14271849039626588357707133 5351943389859970634140175)
              ·
                refine ⟨8027915084789955951210263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5351943389859970634140175 8027915084789955951210263)
                ·
                  refine ⟨12041872627184933926815395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8027915084789955951210263 12041872627184933926815395)
                  ·
                    refine ⟨18062808940777400890223093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12041872627184933926815395 18062808940777400890223093)
                    ·
                      refine ⟨1693388338197881333458415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18062808940777400890223093 1693388338197881333458415)
                      ·
                        rfl

theorem cell23_3297862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_3297862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297862 prefixEnd_3297862 := by exact prefixLift 3297862
  have htrace : WordTrace (prefixWord ++ tailWord_3297862) baseStart_3297862 baseEnd_3297862 := by
    simpa [prefixWord, tailWord_3297862, baseEnd_3297862] using wordTrace_append hprefix tailTrace_3297862
  have hstable : (prefixWord ++ tailWord_3297862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297862).length < 2 ^ (prefixWord ++ tailWord_3297862).sum := by decide
  have hdescent : baseEnd_3297862 < baseStart_3297862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297871 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 5]
def baseStart_3297871 : Nat := 118140960795 + 3297871 * 2 ^ 59
def prefixEnd_3297871 : Nat := 4983230072969 + 3 ^ 40 * 3297871 * 2
def baseEnd_3297871 : Nat := 1693392959523771798245873

theorem tailTrace_3297871 : CollatzResearch.WordTrace tailWord_3297871 prefixEnd_3297871 1693392959523771798245873 := by
  unfold tailWord_3297871
  simp only [CollatzResearch.WordTrace]
  refine ⟨120283237035384073370757467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80188824690256048913838311 120283237035384073370757467)
  ·
    refine ⟨180424855553076110056136201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120283237035384073370757467 180424855553076110056136201)
    ·
      refine ⟨135318641664807082542102151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180424855553076110056136201 135318641664807082542102151)
      ·
        refine ⟨202977962497210623813153227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135318641664807082542102151 202977962497210623813153227)
        ·
          refine ⟨304466943745815935719729841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202977962497210623813153227 304466943745815935719729841)
          ·
            refine ⟨228350207809361951789797381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304466943745815935719729841 228350207809361951789797381)
            ·
              refine ⟨42815663964255365960587009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228350207809361951789797381 42815663964255365960587009)
              ·
                refine ⟨32111747973191524470440257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42815663964255365960587009 32111747973191524470440257)
                ·
                  refine ⟨24083810979893643352830193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32111747973191524470440257 24083810979893643352830193)
                  ·
                    refine ⟨18062858234920232514622645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24083810979893643352830193 18062858234920232514622645)
                    ·
                      refine ⟨1693392959523771798245873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18062858234920232514622645 1693392959523771798245873)
                      ·
                        rfl

theorem cell23_3297871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_3297871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297871 prefixEnd_3297871 := by exact prefixLift 3297871
  have htrace : WordTrace (prefixWord ++ tailWord_3297871) baseStart_3297871 baseEnd_3297871 := by
    simpa [prefixWord, tailWord_3297871, baseEnd_3297871] using wordTrace_append hprefix tailTrace_3297871
  have hstable : (prefixWord ++ tailWord_3297871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297871).length < 2 ^ (prefixWord ++ tailWord_3297871).sum := by decide
  have hdescent : baseEnd_3297871 < baseStart_3297871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297876 : List Nat := [2, 4, 1, 1, 1, 3, 4, 2, 1, 2, 2]
def baseStart_3297876 : Nat := 118140960795 + 3297876 * 2 ^ 59
def prefixEnd_3297876 : Nat := 4983230072969 + 3 ^ 40 * 3297876 * 2
def baseEnd_3297876 : Nat := 1693395526927044278683351

theorem tailTrace_3297876 : CollatzResearch.WordTrace tailWord_3297876 prefixEnd_3297876 1693395526927044278683351 := by
  unfold tailWord_3297876
  simp only [CollatzResearch.WordTrace]
  refine ⟨60141709700182979612344741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80188946266910639483126321 60141709700182979612344741)
  ·
    refine ⟨11276570568784308677314639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60141709700182979612344741 11276570568784308677314639)
    ·
      refine ⟨16914855853176463015971959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11276570568784308677314639 16914855853176463015971959)
      ·
        refine ⟨25372283779764694523957939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16914855853176463015971959 25372283779764694523957939)
        ·
          refine ⟨38058425669647041785936909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25372283779764694523957939 38058425669647041785936909)
          ·
            refine ⟨14271909626117640669726341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38058425669647041785936909 14271909626117640669726341)
            ·
              refine ⟨2675983054897057625573689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14271909626117640669726341 2675983054897057625573689)
              ·
                refine ⟨2006987291172793219180267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2675983054897057625573689 2006987291172793219180267)
                ·
                  refine ⟨3010480936759189828770401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2006987291172793219180267 3010480936759189828770401)
                  ·
                    refine ⟨2257860702569392371577801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3010480936759189828770401 2257860702569392371577801)
                    ·
                      refine ⟨1693395526927044278683351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2257860702569392371577801 1693395526927044278683351)
                      ·
                        rfl

theorem cell23_3297876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_3297876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297876 prefixEnd_3297876 := by exact prefixLift 3297876
  have htrace : WordTrace (prefixWord ++ tailWord_3297876) baseStart_3297876 baseEnd_3297876 := by
    simpa [prefixWord, tailWord_3297876, baseEnd_3297876] using wordTrace_append hprefix tailTrace_3297876
  have hstable : (prefixWord ++ tailWord_3297876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297876).length < 2 ^ (prefixWord ++ tailWord_3297876).sum := by decide
  have hdescent : baseEnd_3297876 < baseStart_3297876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297898 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_3297898 : Nat := 118140960795 + 3297898 * 2 ^ 59
def prefixEnd_3297898 : Nat := 4983230072969 + 3 ^ 40 * 3297898 * 2
def baseEnd_3297898 : Nat := 1693406823501443192608249

theorem tailTrace_3297898 : CollatzResearch.WordTrace tailWord_3297898 prefixEnd_3297898 1693406823501443192608249 := by
  unfold tailWord_3297898
  simp only [CollatzResearch.WordTrace]
  refine ⟨30071055451571564245497587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80189481204190837987993565 30071055451571564245497587)
  ·
    refine ⟨45106583177357346368246381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30071055451571564245497587 45106583177357346368246381)
    ·
      refine ⟨16914968691509004888092393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45106583177357346368246381 16914968691509004888092393)
      ·
        refine ⟨12686226518631753666069295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16914968691509004888092393 12686226518631753666069295)
        ·
          refine ⟨19029339777947630499103943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12686226518631753666069295 19029339777947630499103943)
          ·
            refine ⟨28544009666921445748655915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19029339777947630499103943 28544009666921445748655915)
            ·
              refine ⟨42816014500382168622983873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28544009666921445748655915 42816014500382168622983873)
              ·
                refine ⟨32112010875286626467237905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42816014500382168622983873 32112010875286626467237905)
                ·
                  refine ⟨24084008156464969850428429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32112010875286626467237905 24084008156464969850428429)
                  ·
                    refine ⟨9031503058674363693910661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24084008156464969850428429 9031503058674363693910661)
                    ·
                      refine ⟨1693406823501443192608249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9031503058674363693910661 1693406823501443192608249)
                      ·
                        rfl

theorem cell23_3297898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_3297898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297898 prefixEnd_3297898 := by exact prefixLift 3297898
  have htrace : WordTrace (prefixWord ++ tailWord_3297898) baseStart_3297898 baseEnd_3297898 := by
    simpa [prefixWord, tailWord_3297898, baseEnd_3297898] using wordTrace_append hprefix tailTrace_3297898
  have hstable : (prefixWord ++ tailWord_3297898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297898).length < 2 ^ (prefixWord ++ tailWord_3297898).sum := by decide
  have hdescent : baseEnd_3297898 < baseStart_3297898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297902 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 3, 3, 2]
def baseStart_3297902 : Nat := 118140960795 + 3297902 * 2 ^ 59
def prefixEnd_3297902 : Nat := 4983230072969 + 3 ^ 40 * 3297902 * 2
def baseEnd_3297902 : Nat := 1693408877424061176958231

theorem tailTrace_3297902 : CollatzResearch.WordTrace tailWord_3297902 prefixEnd_3297902 1693408877424061176958231 := by
  unfold tailWord_3297902
  simp only [CollatzResearch.WordTrace]
  refine ⟨15035545962283970708141995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80189578465514510443423973 15035545962283970708141995)
  ·
    refine ⟨22553318943425956062212993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15035545962283970708141995 22553318943425956062212993)
    ·
      refine ⟨16914989207569467046659745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22553318943425956062212993 16914989207569467046659745)
      ·
        refine ⟨12686241905677100284994809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16914989207569467046659745 12686241905677100284994809)
        ·
          refine ⟨9514681429257825213746107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12686241905677100284994809 9514681429257825213746107)
          ·
            refine ⟨14272022143886737820619161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9514681429257825213746107 14272022143886737820619161)
            ·
              refine ⟨10704016607915053365464371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14272022143886737820619161 10704016607915053365464371)
              ·
                refine ⟨16056024911872580048196557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10704016607915053365464371 16056024911872580048196557)
                ·
                  refine ⟨6021009341952217518073709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16056024911872580048196557 6021009341952217518073709)
                  ·
                    refine ⟨2257878503232081569277641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6021009341952217518073709 2257878503232081569277641)
                    ·
                      refine ⟨1693408877424061176958231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2257878503232081569277641 1693408877424061176958231)
                      ·
                        rfl

theorem cell23_3297902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_3297902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297902 prefixEnd_3297902 := by exact prefixLift 3297902
  have htrace : WordTrace (prefixWord ++ tailWord_3297902) baseStart_3297902 baseEnd_3297902 := by
    simpa [prefixWord, tailWord_3297902, baseEnd_3297902] using wordTrace_append hprefix tailTrace_3297902
  have hstable : (prefixWord ++ tailWord_3297902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297902).length < 2 ^ (prefixWord ++ tailWord_3297902).sum := by decide
  have hdescent : baseEnd_3297902 < baseStart_3297902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297931 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 9]
def baseStart_3297931 : Nat := 118140960795 + 3297931 * 2 ^ 59
def prefixEnd_3297931 : Nat := 4983230072969 + 3 ^ 40 * 3297931 * 2
def baseEnd_3297931 : Nat := 1693423768363041563495597

theorem tailTrace_3297931 : CollatzResearch.WordTrace tailWord_3297931 prefixEnd_3297931 1693423768363041563495597 := by
  unfold tailWord_3297931
  simp only [CollatzResearch.WordTrace]
  refine ⟨120285425415166703617941647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80190283610111135745294431 120285425415166703617941647)
  ·
    refine ⟨180428138122750055426912471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120285425415166703617941647 180428138122750055426912471)
    ·
      refine ⟨270642207184125083140368707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180428138122750055426912471 270642207184125083140368707)
      ·
        refine ⟨405963310776187624710553061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270642207184125083140368707 405963310776187624710553061)
        ·
          refine ⟨76118120770535179633228699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 405963310776187624710553061 76118120770535179633228699)
          ·
            refine ⟨114177181155802769449843049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76118120770535179633228699 114177181155802769449843049)
            ·
              refine ⟨85632885866852077087382287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114177181155802769449843049 85632885866852077087382287)
              ·
                refine ⟨128449328800278115631073431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85632885866852077087382287 128449328800278115631073431)
                ·
                  refine ⟨192673993200417173446610147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128449328800278115631073431 192673993200417173446610147)
                  ·
                    refine ⟨289010989800625760169915221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 192673993200417173446610147 289010989800625760169915221)
                    ·
                      refine ⟨1693423768363041563495597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 289010989800625760169915221 1693423768363041563495597)
                      ·
                        rfl

theorem cell23_3297931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 9].length) (baseStart_3297931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297931 prefixEnd_3297931 := by exact prefixLift 3297931
  have htrace : WordTrace (prefixWord ++ tailWord_3297931) baseStart_3297931 baseEnd_3297931 := by
    simpa [prefixWord, tailWord_3297931, baseEnd_3297931] using wordTrace_append hprefix tailTrace_3297931
  have hstable : (prefixWord ++ tailWord_3297931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297931).length < 2 ^ (prefixWord ++ tailWord_3297931).sum := by decide
  have hdescent : baseEnd_3297931 < baseStart_3297931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297932 : List Nat := [2, 2, 1, 2, 1, 1, 2, 6, 2, 2, 2]
def baseStart_3297932 : Nat := 118140960795 + 3297932 * 2 ^ 59
def prefixEnd_3297932 : Nat := 4983230072969 + 3 ^ 40 * 3297932 * 2
def baseEnd_3297932 : Nat := 1693424281843696059583093

theorem tailTrace_3297932 : CollatzResearch.WordTrace tailWord_3297932 prefixEnd_3297932 1693424281843696059583093 := by
  unfold tailWord_3297932
  simp only [CollatzResearch.WordTrace]
  refine ⟨60142730944081540394364025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80190307925442053859152033 60142730944081540394364025)
  ·
    refine ⟨45107048208061155295773019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60142730944081540394364025 45107048208061155295773019)
    ·
      refine ⟨67660572312091732943659529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45107048208061155295773019 67660572312091732943659529)
      ·
        refine ⟨50745429234068799707744647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67660572312091732943659529 50745429234068799707744647)
        ·
          refine ⟨76118143851103199561616971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50745429234068799707744647 76118143851103199561616971)
          ·
            refine ⟨114177215776654799342425457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76118143851103199561616971 114177215776654799342425457)
            ·
              refine ⟨85632911832491099506819093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114177215776654799342425457 85632911832491099506819093)
              ·
                refine ⟨4014042742148020289382145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85632911832491099506819093 4014042742148020289382145)
                ·
                  refine ⟨3010532056611015217036609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4014042742148020289382145 3010532056611015217036609)
                  ·
                    refine ⟨2257899042458261412777457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3010532056611015217036609 2257899042458261412777457)
                    ·
                      refine ⟨1693424281843696059583093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2257899042458261412777457 1693424281843696059583093)
                      ·
                        rfl

theorem cell23_3297932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_3297932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297932 prefixEnd_3297932 := by exact prefixLift 3297932
  have htrace : WordTrace (prefixWord ++ tailWord_3297932) baseStart_3297932 baseEnd_3297932 := by
    simpa [prefixWord, tailWord_3297932, baseEnd_3297932] using wordTrace_append hprefix tailTrace_3297932
  have hstable : (prefixWord ++ tailWord_3297932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297932).length < 2 ^ (prefixWord ++ tailWord_3297932).sum := by decide
  have hdescent : baseEnd_3297932 < baseStart_3297932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297968 : List Nat := [2, 1, 1, 1, 2, 1, 3, 5, 2, 5]
def baseStart_3297968 : Nat := 118140960795 + 3297968 * 2 ^ 59
def prefixEnd_3297968 : Nat := 4983230072969 + 3 ^ 40 * 3297968 * 2
def baseEnd_3297968 : Nat := 564480922382419306244309

theorem tailTrace_3297968 : CollatzResearch.WordTrace tailWord_3297968 prefixEnd_3297968 564480922382419306244309 := by
  unfold tailWord_3297968
  simp only [CollatzResearch.WordTrace]
  refine ⟨60143387458016329468519279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80191183277355105958025705 60143387458016329468519279)
  ·
    refine ⟨90215081187024494202778919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60143387458016329468519279 90215081187024494202778919)
    ·
      refine ⟨135322621780536741304168379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90215081187024494202778919 135322621780536741304168379)
      ·
        refine ⟨202983932670805111956252569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135322621780536741304168379 202983932670805111956252569)
        ·
          refine ⟨152237949503103833967189427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202983932670805111956252569 152237949503103833967189427)
          ·
            refine ⟨228356924254655750950784141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152237949503103833967189427 228356924254655750950784141)
            ·
              refine ⟨85633846595495906606544053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228356924254655750950784141 85633846595495906606544053)
              ·
                refine ⟨8028173118327741244363505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85633846595495906606544053 8028173118327741244363505)
                ·
                  refine ⟨6021129838745805933272629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8028173118327741244363505 6021129838745805933272629)
                  ·
                    refine ⟨564480922382419306244309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6021129838745805933272629 564480922382419306244309)
                    ·
                      rfl

theorem cell23_3297968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 2, 5].length) (baseStart_3297968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297968 prefixEnd_3297968 := by exact prefixLift 3297968
  have htrace : WordTrace (prefixWord ++ tailWord_3297968) baseStart_3297968 baseEnd_3297968 := by
    simpa [prefixWord, tailWord_3297968, baseEnd_3297968] using wordTrace_append hprefix tailTrace_3297968
  have hstable : (prefixWord ++ tailWord_3297968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297968).length < 2 ^ (prefixWord ++ tailWord_3297968).sum := by decide
  have hdescent : baseEnd_3297968 < baseStart_3297968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297978 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5]
def baseStart_3297978 : Nat := 118140960795 + 3297978 * 2 ^ 59
def prefixEnd_3297978 : Nat := 4983230072969 + 3 ^ 40 * 3297978 * 2
def baseEnd_3297978 : Nat := 1693447901953802879607881

theorem tailTrace_3297978 : CollatzResearch.WordTrace tailWord_3297978 prefixEnd_3297978 1693447901953802879607881 := by
  unfold tailWord_3297978
  simp only [CollatzResearch.WordTrace]
  refine ⟨30071784911499107661225647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80191426430664287096601725 30071784911499107661225647)
  ·
    refine ⟨45107677367248661491838471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30071784911499107661225647 45107677367248661491838471)
    ·
      refine ⟨67661516050872992237757707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45107677367248661491838471 67661516050872992237757707)
      ·
        refine ⟨101492274076309488356636561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67661516050872992237757707 101492274076309488356636561)
        ·
          refine ⟨76119205557232116267477421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101492274076309488356636561 76119205557232116267477421)
          ·
            refine ⟨28544702083962043600304033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76119205557232116267477421 28544702083962043600304033)
            ·
              refine ⟨21408526562971532700228025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28544702083962043600304033 21408526562971532700228025)
              ·
                refine ⟨16056394922228649525171019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21408526562971532700228025 16056394922228649525171019)
                ·
                  refine ⟨24084592383342974287756529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16056394922228649525171019 24084592383342974287756529)
                  ·
                    refine ⟨18063444287507230715817397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24084592383342974287756529 18063444287507230715817397)
                    ·
                      refine ⟨1693447901953802879607881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18063444287507230715817397 1693447901953802879607881)
                      ·
                        rfl

theorem cell23_3297978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_3297978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3297978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3297978 prefixEnd_3297978 := by exact prefixLift 3297978
  have htrace : WordTrace (prefixWord ++ tailWord_3297978) baseStart_3297978 baseEnd_3297978 := by
    simpa [prefixWord, tailWord_3297978, baseEnd_3297978] using wordTrace_append hprefix tailTrace_3297978
  have hstable : (prefixWord ++ tailWord_3297978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297978).length < 2 ^ (prefixWord ++ tailWord_3297978).sum := by decide
  have hdescent : baseEnd_3297978 < baseStart_3297978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298025 : List Nat := [1, 2, 1, 1, 1, 2, 5, 3, 2, 2, 3]
def baseStart_3298025 : Nat := 118140960795 + 3298025 * 2 ^ 59
def prefixEnd_3298025 : Nat := 4983230072969 + 3 ^ 40 * 3298025 * 2
def baseEnd_3298025 : Nat := 1693472035544564195720165

theorem tailTrace_3298025 : CollatzResearch.WordTrace tailWord_3298025 prefixEnd_3298025 1693472035544564195720165 := by
  unfold tailWord_3298025
  simp only [CollatzResearch.WordTrace]
  refine ⟨120288853876826157671863529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80192569251217438447909019 120288853876826157671863529)
  ·
    refine ⟨90216640407619618253897647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120288853876826157671863529 90216640407619618253897647)
    ·
      refine ⟨135324960611429427380846471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90216640407619618253897647 135324960611429427380846471)
      ·
        refine ⟨202987440917144141071269707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135324960611429427380846471 202987440917144141071269707)
        ·
          refine ⟨304481161375716211606904561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202987440917144141071269707 304481161375716211606904561)
          ·
            refine ⟨228360871031787158705178421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304481161375716211606904561 228360871031787158705178421)
            ·
              refine ⟨21408831659230046128610477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 228360871031787158705178421 21408831659230046128610477)
              ·
                refine ⟨8028311872211267298228929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21408831659230046128610477 8028311872211267298228929)
                ·
                  refine ⟨6021233904158450473671697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8028311872211267298228929 6021233904158450473671697)
                  ·
                    refine ⟨4515925428118837855253773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6021233904158450473671697 4515925428118837855253773)
                    ·
                      refine ⟨1693472035544564195720165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4515925428118837855253773 1693472035544564195720165)
                      ·
                        rfl

theorem cell23_3298025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 2, 3].length) (baseStart_3298025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298025 prefixEnd_3298025 := by exact prefixLift 3298025
  have htrace : WordTrace (prefixWord ++ tailWord_3298025) baseStart_3298025 baseEnd_3298025 := by
    simpa [prefixWord, tailWord_3298025, baseEnd_3298025] using wordTrace_append hprefix tailTrace_3298025
  have hstable : (prefixWord ++ tailWord_3298025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298025).length < 2 ^ (prefixWord ++ tailWord_3298025).sum := by decide
  have hdescent : baseEnd_3298025 < baseStart_3298025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298032 : List Nat := [2, 1, 1, 1, 3, 1, 4, 5, 1, 4]
def baseStart_3298032 : Nat := 118140960795 + 3298032 * 2 ^ 59
def prefixEnd_3298032 : Nat := 4983230072969 + 3 ^ 40 * 3298032 * 2
def baseEnd_3298032 : Nat := 564491876636381889444211

theorem tailTrace_3298032 : CollatzResearch.WordTrace tailWord_3298032 prefixEnd_3298032 564491876636381889444211 := by
  unfold tailWord_3298032
  simp only [CollatzResearch.WordTrace]
  refine ⟨60144554593900398933684175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80192739458533865244912233 60144554593900398933684175)
  ·
    refine ⟨90216831890850598400526263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60144554593900398933684175 90216831890850598400526263)
    ·
      refine ⟨135325247836275897600789395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90216831890850598400526263 135325247836275897600789395)
      ·
        refine ⟨202987871754413846401184093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135325247836275897600789395 202987871754413846401184093)
        ·
          refine ⟨76120451907905192400444035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202987871754413846401184093 76120451907905192400444035)
          ·
            refine ⟨114180677861857788600666053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76120451907905192400444035 114180677861857788600666053)
            ·
              refine ⟨21408877099098335362624885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114180677861857788600666053 21408877099098335362624885)
              ·
                refine ⟨2007082228040468940246083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21408877099098335362624885 2007082228040468940246083)
                ·
                  refine ⟨3010623342060703410369125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2007082228040468940246083 3010623342060703410369125)
                  ·
                    refine ⟨564491876636381889444211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3010623342060703410369125 564491876636381889444211)
                    ·
                      rfl

theorem cell23_3298032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 1, 4].length) (baseStart_3298032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298032 prefixEnd_3298032 := by exact prefixLift 3298032
  have htrace : WordTrace (prefixWord ++ tailWord_3298032) baseStart_3298032 baseEnd_3298032 := by
    simpa [prefixWord, tailWord_3298032, baseEnd_3298032] using wordTrace_append hprefix tailTrace_3298032
  have hstable : (prefixWord ++ tailWord_3298032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298032).length < 2 ^ (prefixWord ++ tailWord_3298032).sum := by decide
  have hdescent : baseEnd_3298032 < baseStart_3298032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298045 : List Nat := [1, 4, 1, 1, 1, 1, 6, 2, 6]
def baseStart_3298045 : Nat := 118140960795 + 3298045 * 2 ^ 59
def prefixEnd_3298045 : Nat := 4983230072969 + 3 ^ 40 * 3298045 * 2
def baseEnd_3298045 : Nat := 188164700573072679718897

theorem tailTrace_3298045 : CollatzResearch.WordTrace tailWord_3298045 prefixEnd_3298045 188164700573072679718897 := by
  unfold tailWord_3298045
  simp only [CollatzResearch.WordTrace]
  refine ⟨120289583336753701087591589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80193055557835800725061059 120289583336753701087591589)
  ·
    refine ⟨22554296875641318953923423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120289583336753701087591589 22554296875641318953923423)
    ·
      refine ⟨33831445313461978430885135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22554296875641318953923423 33831445313461978430885135)
      ·
        refine ⟨50747167970192967646327703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33831445313461978430885135 50747167970192967646327703)
        ·
          refine ⟨76120751955289451469491555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50747167970192967646327703 76120751955289451469491555)
          ·
            refine ⟨114181127932934177204237333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76120751955289451469491555 114181127932934177204237333)
            ·
              refine ⟨5352240371856289556448625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114181127932934177204237333 5352240371856289556448625)
              ·
                refine ⟨4014180278892217167336469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5352240371856289556448625 4014180278892217167336469)
                ·
                  refine ⟨188164700573072679718897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4014180278892217167336469 188164700573072679718897)
                  ·
                    rfl

theorem cell23_3298045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_3298045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298045 prefixEnd_3298045 := by exact prefixLift 3298045
  have htrace : WordTrace (prefixWord ++ tailWord_3298045) baseStart_3298045 baseEnd_3298045 := by
    simpa [prefixWord, tailWord_3298045, baseEnd_3298045] using wordTrace_append hprefix tailTrace_3298045
  have hstable : (prefixWord ++ tailWord_3298045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298045).length < 2 ^ (prefixWord ++ tailWord_3298045).sum := by decide
  have hdescent : baseEnd_3298045 < baseStart_3298045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298115 : List Nat := [1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 5]
def baseStart_3298115 : Nat := 118140960795 + 3298115 * 2 ^ 59
def prefixEnd_3298115 : Nat := 4983230072969 + 3 ^ 40 * 3298115 * 2
def baseEnd_3298115 : Nat := 1693518248803468843594751

theorem tailTrace_3298115 : CollatzResearch.WordTrace tailWord_3298115 prefixEnd_3298115 1693518248803468843594751 := by
  unfold tailWord_3298115
  simp only [CollatzResearch.WordTrace]
  refine ⟨120292136446500103042639799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80194757631000068695093199 120292136446500103042639799)
  ·
    refine ⟨180438204669750154563959699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120292136446500103042639799 180438204669750154563959699)
    ·
      refine ⟨270657307004625231845939549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180438204669750154563959699 270657307004625231845939549)
      ·
        refine ⟨101496490126734461942227331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270657307004625231845939549 101496490126734461942227331)
        ·
          refine ⟨152244735190101692913340997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101496490126734461942227331 152244735190101692913340997)
          ·
            refine ⟨28545887848144067421251437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152244735190101692913340997 28545887848144067421251437)
            ·
              refine ⟨10704707943054025282969289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28545887848144067421251437 10704707943054025282969289)
              ·
                refine ⟨8028530957290518962226967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10704707943054025282969289 8028530957290518962226967)
                ·
                  refine ⟨12042796435935778443340451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8028530957290518962226967 12042796435935778443340451)
                  ·
                    refine ⟨18064194653903667665010677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12042796435935778443340451 18064194653903667665010677)
                    ·
                      refine ⟨1693518248803468843594751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18064194653903667665010677 1693518248803468843594751)
                      ·
                        rfl

theorem cell23_3298115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_3298115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298115 prefixEnd_3298115 := by exact prefixLift 3298115
  have htrace : WordTrace (prefixWord ++ tailWord_3298115) baseStart_3298115 baseEnd_3298115 := by
    simpa [prefixWord, tailWord_3298115, baseEnd_3298115] using wordTrace_append hprefix tailTrace_3298115
  have hstable : (prefixWord ++ tailWord_3298115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298115).length < 2 ^ (prefixWord ++ tailWord_3298115).sum := by decide
  have hdescent : baseEnd_3298115 < baseStart_3298115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298129 : List Nat := [1, 2, 2, 1, 6, 1, 2, 2, 1, 1, 4]
def baseStart_3298129 : Nat := 118140960795 + 3298129 * 2 ^ 59
def prefixEnd_3298129 : Nat := 4983230072969 + 3 ^ 40 * 3298129 * 2
def baseEnd_3298129 : Nat := 1693525437532631788819687

theorem tailTrace_3298129 : CollatzResearch.WordTrace tailWord_3298129 prefixEnd_3298129 1693525437532631788819687 := by
  unfold tailWord_3298129
  simp only [CollatzResearch.WordTrace]
  refine ⟨120292647068449383433649441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80195098045632922289099627 120292647068449383433649441)
  ·
    refine ⟨90219485301337037575237081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120292647068449383433649441 90219485301337037575237081)
    ·
      refine ⟨67664613976002778181427811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90219485301337037575237081 67664613976002778181427811)
      ·
        refine ⟨101496920964004167272141717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67664613976002778181427811 101496920964004167272141717)
        ·
          refine ⟨4757668170187695340881643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101496920964004167272141717 4757668170187695340881643)
          ·
            refine ⟨7136502255281543011322465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4757668170187695340881643 7136502255281543011322465)
            ·
              refine ⟨5352376691461157258491849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7136502255281543011322465 5352376691461157258491849)
              ·
                refine ⟨4014282518595867943868887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5352376691461157258491849 4014282518595867943868887)
                ·
                  refine ⟨6021423777893801915803331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4014282518595867943868887 6021423777893801915803331)
                  ·
                    refine ⟨9032135666840702873704997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6021423777893801915803331 9032135666840702873704997)
                    ·
                      refine ⟨1693525437532631788819687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9032135666840702873704997 1693525437532631788819687)
                      ·
                        rfl

theorem cell23_3298129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 1, 4].length) (baseStart_3298129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298129 prefixEnd_3298129 := by exact prefixLift 3298129
  have htrace : WordTrace (prefixWord ++ tailWord_3298129) baseStart_3298129 baseEnd_3298129 := by
    simpa [prefixWord, tailWord_3298129, baseEnd_3298129] using wordTrace_append hprefix tailTrace_3298129
  have hstable : (prefixWord ++ tailWord_3298129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298129).length < 2 ^ (prefixWord ++ tailWord_3298129).sum := by decide
  have hdescent : baseEnd_3298129 < baseStart_3298129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298135 : List Nat := [1, 1, 3, 2, 4, 2, 1, 9]
def baseStart_3298135 : Nat := 118140960795 + 3298135 * 2 ^ 59
def prefixEnd_3298135 : Nat := 4983230072969 + 3 ^ 40 * 3298135 * 2
def baseEnd_3298135 : Nat := 62723278459872546864617

theorem tailTrace_3298135 : CollatzResearch.WordTrace tailWord_3298135 prefixEnd_3298135 62723278459872546864617 := by
  unfold tailWord_3298135
  simp only [CollatzResearch.WordTrace]
  refine ⟨120292865906427646458367859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80195243937618430972245239 120292865906427646458367859)
  ·
    refine ⟨180439298859641469687551789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120292865906427646458367859 180439298859641469687551789)
    ·
      refine ⟨67664737072365551132831921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180439298859641469687551789 67664737072365551132831921)
      ·
        refine ⟨50748552804274163349623941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67664737072365551132831921 50748552804274163349623941)
        ·
          refine ⟨9515353650801405628054489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50748552804274163349623941 9515353650801405628054489)
          ·
            refine ⟨7136515238101054221040867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9515353650801405628054489 7136515238101054221040867)
            ·
              refine ⟨10704772857151581331561301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7136515238101054221040867 10704772857151581331561301)
              ·
                refine ⟨62723278459872546864617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10704772857151581331561301 62723278459872546864617)
                ·
                  rfl

theorem cell23_3298135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 9].length) (baseStart_3298135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298135 prefixEnd_3298135 := by exact prefixLift 3298135
  have htrace : WordTrace (prefixWord ++ tailWord_3298135) baseStart_3298135 baseEnd_3298135 := by
    simpa [prefixWord, tailWord_3298135, baseEnd_3298135] using wordTrace_append hprefix tailTrace_3298135
  have hstable : (prefixWord ++ tailWord_3298135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298135).length < 2 ^ (prefixWord ++ tailWord_3298135).sum := by decide
  have hdescent : baseEnd_3298135 < baseStart_3298135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298179 : List Nat := [1, 1, 1, 3, 4, 1, 3, 3, 2, 1, 3]
def baseStart_3298179 : Nat := 118140960795 + 3298179 * 2 ^ 59
def prefixEnd_3298179 : Nat := 4983230072969 + 3 ^ 40 * 3298179 * 2
def baseEnd_3298179 : Nat := 1693551111565356593194457

theorem tailTrace_3298179 : CollatzResearch.WordTrace tailWord_3298179 prefixEnd_3298179 1693551111565356593194457 := by
  unfold tailWord_3298179
  simp only [CollatzResearch.WordTrace]
  refine ⟨120294470718268241972969591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80196313812178827981979727 120294470718268241972969591)
  ·
    refine ⟨180441706077402362959454387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120294470718268241972969591 180441706077402362959454387)
    ·
      refine ⟨270662559116103544439181581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180441706077402362959454387 270662559116103544439181581)
      ·
        refine ⟨101498459668538829164693093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270662559116103544439181581 101498459668538829164693093)
        ·
          refine ⟨19030961187851030468379955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101498459668538829164693093 19030961187851030468379955)
          ·
            refine ⟨28546441781776545702569933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19030961187851030468379955 28546441781776545702569933)
            ·
              refine ⟨10704915668166204638463725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28546441781776545702569933 10704915668166204638463725)
              ·
                refine ⟨4014343375562326739423897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10704915668166204638463725 4014343375562326739423897)
                ·
                  refine ⟨3010757531671745054567923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4014343375562326739423897 3010757531671745054567923)
                  ·
                    refine ⟨4516136297507617581851885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3010757531671745054567923 4516136297507617581851885)
                    ·
                      refine ⟨1693551111565356593194457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4516136297507617581851885 1693551111565356593194457)
                      ·
                        rfl

theorem cell23_3298179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 1, 3].length) (baseStart_3298179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298179 prefixEnd_3298179 := by exact prefixLift 3298179
  have htrace : WordTrace (prefixWord ++ tailWord_3298179) baseStart_3298179 baseEnd_3298179 := by
    simpa [prefixWord, tailWord_3298179, baseEnd_3298179] using wordTrace_append hprefix tailTrace_3298179
  have hstable : (prefixWord ++ tailWord_3298179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298179).length < 2 ^ (prefixWord ++ tailWord_3298179).sum := by decide
  have hdescent : baseEnd_3298179 < baseStart_3298179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298230 : List Nat := [5, 1, 4, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_3298230 : Nat := 118140960795 + 3298230 * 2 ^ 59
def prefixEnd_3298230 : Nat := 4983230072969 + 3 ^ 40 * 3298230 * 2
def baseEnd_3298230 : Nat := 1693577299078735893656723

theorem tailTrace_3298230 : CollatzResearch.WordTrace tailWord_3298230 prefixEnd_3298230 1693577299078735893656723 := by
  unfold tailWord_3298230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7518520677567717355192259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80197553894055651788717429 7518520677567717355192259)
  ·
    refine ⟨11277781016351576032788389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7518520677567717355192259 11277781016351576032788389)
    ·
      refine ⟨2114583940565920506147823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11277781016351576032788389 2114583940565920506147823)
      ·
        refine ⟨3171875910848880759221735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2114583940565920506147823 3171875910848880759221735)
        ·
          refine ⟨4757813866273321138832603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3171875910848880759221735 4757813866273321138832603)
          ·
            refine ⟨7136720799409981708248905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4757813866273321138832603 7136720799409981708248905)
            ·
              refine ⟨5352540599557486281186679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7136720799409981708248905 5352540599557486281186679)
              ·
                refine ⟨8028810899336229421780019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5352540599557486281186679 8028810899336229421780019)
                ·
                  refine ⟨12043216349004344132670029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8028810899336229421780019 12043216349004344132670029)
                  ·
                    refine ⟨4516206130876629049751261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12043216349004344132670029 4516206130876629049751261)
                    ·
                      refine ⟨1693577299078735893656723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4516206130876629049751261 1693577299078735893656723)
                      ·
                        rfl

theorem cell23_3298230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_3298230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298230 prefixEnd_3298230 := by exact prefixLift 3298230
  have htrace : WordTrace (prefixWord ++ tailWord_3298230) baseStart_3298230 baseEnd_3298230 := by
    simpa [prefixWord, tailWord_3298230, baseEnd_3298230] using wordTrace_append hprefix tailTrace_3298230
  have hstable : (prefixWord ++ tailWord_3298230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298230).length < 2 ^ (prefixWord ++ tailWord_3298230).sum := by decide
  have hdescent : baseEnd_3298230 < baseStart_3298230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298232 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 2, 2, 4]
def baseStart_3298232 : Nat := 118140960795 + 3298232 * 2 ^ 59
def prefixEnd_3298232 : Nat := 4983230072969 + 3 ^ 40 * 3298232 * 2
def baseEnd_3298232 : Nat := 1693578326040044885831713

theorem tailTrace_3298232 : CollatzResearch.WordTrace tailWord_3298232 prefixEnd_3298232 1693578326040044885831713 := by
  unfold tailWord_3298232
  simp only [CollatzResearch.WordTrace]
  refine ⟨60148201893538116012324475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80197602524717488016432633 60148201893538116012324475)
  ·
    refine ⟨90222302840307174018486713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60148201893538116012324475 90222302840307174018486713)
    ·
      refine ⟨67666727130230380513865035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90222302840307174018486713 67666727130230380513865035)
      ·
        refine ⟨101500090695345570770797553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67666727130230380513865035 101500090695345570770797553)
        ·
          refine ⟨76125068021509178078098165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101500090695345570770797553 76125068021509178078098165)
          ·
            refine ⟨7136725127016485444821703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76125068021509178078098165 7136725127016485444821703)
            ·
              refine ⟨10705087690524728167232555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7136725127016485444821703 10705087690524728167232555)
              ·
                refine ⟨16057631535787092250848833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10705087690524728167232555 16057631535787092250848833)
                ·
                  refine ⟨12043223651840319188136625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16057631535787092250848833 12043223651840319188136625)
                  ·
                    refine ⟨9032417738880239391102469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12043223651840319188136625 9032417738880239391102469)
                    ·
                      refine ⟨1693578326040044885831713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9032417738880239391102469 1693578326040044885831713)
                      ·
                        rfl

theorem cell23_3298232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_3298232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298232 prefixEnd_3298232 := by exact prefixLift 3298232
  have htrace : WordTrace (prefixWord ++ tailWord_3298232) baseStart_3298232 baseEnd_3298232 := by
    simpa [prefixWord, tailWord_3298232, baseEnd_3298232] using wordTrace_append hprefix tailTrace_3298232
  have hstable : (prefixWord ++ tailWord_3298232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298232).length < 2 ^ (prefixWord ++ tailWord_3298232).sum := by decide
  have hdescent : baseEnd_3298232 < baseStart_3298232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298252 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 1, 5, 3]
def baseStart_3298252 : Nat := 118140960795 + 3298252 * 2 ^ 59
def prefixEnd_3298252 : Nat := 4983230072969 + 3 ^ 40 * 3298252 * 2
def baseEnd_3298252 : Nat := 1693588595653134807581621

theorem tailTrace_3298252 : CollatzResearch.WordTrace tailWord_3298252 prefixEnd_3298252 1693588595653134807581621 := by
  unfold tailWord_3298252
  simp only [CollatzResearch.WordTrace]
  refine ⟨60148566623501887720188505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80198088831335850293584673 60148566623501887720188505)
  ·
    refine ⟨45111424967626415790141379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60148566623501887720188505 45111424967626415790141379)
    ·
      refine ⟨67667137451439623685212069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45111424967626415790141379 67667137451439623685212069)
      ·
        refine ⟨12687588272144929440977263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67667137451439623685212069 12687588272144929440977263)
        ·
          refine ⟨19031382408217394161465895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12687588272144929440977263 19031382408217394161465895)
          ·
            refine ⟨28547073612326091242198843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19031382408217394161465895 28547073612326091242198843)
            ·
              refine ⟨42820610418489136863298265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28547073612326091242198843 42820610418489136863298265)
              ·
                refine ⟨32115457813866852647473699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42820610418489136863298265 32115457813866852647473699)
                ·
                  refine ⟨48173186720800278971210549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32115457813866852647473699 48173186720800278971210549)
                  ·
                    refine ⟨4516236255075026153550989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48173186720800278971210549 4516236255075026153550989)
                    ·
                      refine ⟨1693588595653134807581621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4516236255075026153550989 1693588595653134807581621)
                      ·
                        rfl

theorem cell23_3298252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_3298252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298252 prefixEnd_3298252 := by exact prefixLift 3298252
  have htrace : WordTrace (prefixWord ++ tailWord_3298252) baseStart_3298252 baseEnd_3298252 := by
    simpa [prefixWord, tailWord_3298252, baseEnd_3298252] using wordTrace_append hprefix tailTrace_3298252
  have hstable : (prefixWord ++ tailWord_3298252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298252).length < 2 ^ (prefixWord ++ tailWord_3298252).sum := by decide
  have hdescent : baseEnd_3298252 < baseStart_3298252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298269 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_3298269 : Nat := 118140960795 + 3298269 * 2 ^ 59
def prefixEnd_3298269 : Nat := 4983230072969 + 3 ^ 40 * 3298269 * 2
def baseEnd_3298269 : Nat := 1693597324824261241069043

theorem tailTrace_3298269 : CollatzResearch.WordTrace tailWord_3298269 prefixEnd_3298269 1693597324824261241069043 := by
  unfold tailWord_3298269
  simp only [CollatzResearch.WordTrace]
  refine ⟨120297753287942187343745861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80198502191961458229163907 120297753287942187343745861)
  ·
    refine ⟨22555828741489160126952349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120297753287942187343745861 22555828741489160126952349)
    ·
      refine ⟨8458435778058435047607131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22555828741489160126952349 8458435778058435047607131)
      ·
        refine ⟨12687653667087652571410697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8458435778058435047607131 12687653667087652571410697)
        ·
          refine ⟨9515740250315739428558023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12687653667087652571410697 9515740250315739428558023)
          ·
            refine ⟨14273610375473609142837035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9515740250315739428558023 14273610375473609142837035)
            ·
              refine ⟨21410415563210413714255553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14273610375473609142837035 21410415563210413714255553)
              ·
                refine ⟨16057811672407810285691665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21410415563210413714255553 16057811672407810285691665)
                ·
                  refine ⟨12043358754305857714268749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16057811672407810285691665 12043358754305857714268749)
                  ·
                    refine ⟨4516259532864696642850781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12043358754305857714268749 4516259532864696642850781)
                    ·
                      refine ⟨1693597324824261241069043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4516259532864696642850781 1693597324824261241069043)
                      ·
                        rfl

theorem cell23_3298269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_3298269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298269 prefixEnd_3298269 := by exact prefixLift 3298269
  have htrace : WordTrace (prefixWord ++ tailWord_3298269) baseStart_3298269 baseEnd_3298269 := by
    simpa [prefixWord, tailWord_3298269, baseEnd_3298269] using wordTrace_append hprefix tailTrace_3298269
  have hstable : (prefixWord ++ tailWord_3298269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298269).length < 2 ^ (prefixWord ++ tailWord_3298269).sum := by decide
  have hdescent : baseEnd_3298269 < baseStart_3298269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298359 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 5, 1, 3]
def baseStart_3298359 : Nat := 118140960795 + 3298359 * 2 ^ 59
def prefixEnd_3298359 : Nat := 4983230072969 + 3 ^ 40 * 3298359 * 2
def baseEnd_3298359 : Nat := 1693643538083165888943629

theorem tailTrace_3298359 : CollatzResearch.WordTrace tailWord_3298359 prefixEnd_3298359 1693643538083165888943629 := by
  unfold tailWord_3298359
  simp only [CollatzResearch.WordTrace]
  refine ⟨120301035857616132714522131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80200690571744088476348087 120301035857616132714522131)
  ·
    refine ⟨180451553786424199071783197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120301035857616132714522131 180451553786424199071783197)
    ·
      refine ⟨67669332669909074651918699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180451553786424199071783197 67669332669909074651918699)
      ·
        refine ⟨101503999004863611977878049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67669332669909074651918699 101503999004863611977878049)
        ·
          refine ⟨76127999253647708983408537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101503999004863611977878049 76127999253647708983408537)
          ·
            refine ⟨57095999440235781737556403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76127999253647708983408537 57095999440235781737556403)
            ·
              refine ⟨85643999160353672606334605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57095999440235781737556403 85643999160353672606334605)
              ·
                refine ⟨32116499685132627227375477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85643999160353672606334605 32116499685132627227375477)
                ·
                  refine ⟨3010921845481183802566451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32116499685132627227375477 3010921845481183802566451)
                  ·
                    refine ⟨4516382768221775703849677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3010921845481183802566451 4516382768221775703849677)
                    ·
                      refine ⟨1693643538083165888943629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4516382768221775703849677 1693643538083165888943629)
                      ·
                        rfl

theorem cell23_3298359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 1, 3].length) (baseStart_3298359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298359 prefixEnd_3298359 := by exact prefixLift 3298359
  have htrace : WordTrace (prefixWord ++ tailWord_3298359) baseStart_3298359 baseEnd_3298359 := by
    simpa [prefixWord, tailWord_3298359, baseEnd_3298359] using wordTrace_append hprefix tailTrace_3298359
  have hstable : (prefixWord ++ tailWord_3298359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298359).length < 2 ^ (prefixWord ++ tailWord_3298359).sum := by decide
  have hdescent : baseEnd_3298359 < baseStart_3298359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298392 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 3, 6]
def baseStart_3298392 : Nat := 118140960795 + 3298392 * 2 ^ 59
def prefixEnd_3298392 : Nat := 4983230072969 + 3 ^ 40 * 3298392 * 2
def baseEnd_3298392 : Nat := 564553494314921419943659

theorem tailTrace_3298392 : CollatzResearch.WordTrace tailWord_3298392 prefixEnd_3298392 564553494314921419943659 := by
  unfold tailWord_3298392
  simp only [CollatzResearch.WordTrace]
  refine ⟨60151119733248289675236715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80201492977664386233648953 60151119733248289675236715)
  ·
    refine ⟨90226679599872434512855073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60151119733248289675236715 90226679599872434512855073)
    ·
      refine ⟨67670009699904325884641305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90226679599872434512855073 67670009699904325884641305)
      ·
        refine ⟨50752507274928244413480979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67670009699904325884641305 50752507274928244413480979)
        ·
          refine ⟨76128760912392366620221469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50752507274928244413480979 76128760912392366620221469)
          ·
            refine ⟨28548285342147137482583051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76128760912392366620221469 28548285342147137482583051)
            ·
              refine ⟨42822428013220706223874577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28548285342147137482583051 42822428013220706223874577)
              ·
                refine ⟨32116821009915529667905933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42822428013220706223874577 32116821009915529667905933)
                ·
                  refine ⟨12043807878718323625464725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32116821009915529667905933 12043807878718323625464725)
                  ·
                    refine ⟨564553494314921419943659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12043807878718323625464725 564553494314921419943659)
                    ·
                      rfl

theorem cell23_3298392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_3298392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298392 prefixEnd_3298392 := by exact prefixLift 3298392
  have htrace : WordTrace (prefixWord ++ tailWord_3298392) baseStart_3298392 baseEnd_3298392 := by
    simpa [prefixWord, tailWord_3298392, baseEnd_3298392] using wordTrace_append hprefix tailTrace_3298392
  have hstable : (prefixWord ++ tailWord_3298392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298392).length < 2 ^ (prefixWord ++ tailWord_3298392).sum := by decide
  have hdescent : baseEnd_3298392 < baseStart_3298392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298409 : List Nat := [1, 2, 1, 1, 1, 7, 2, 1, 1, 6]
def baseStart_3298409 : Nat := 118140960795 + 3298409 * 2 ^ 59
def prefixEnd_3298409 : Nat := 4983230072969 + 3 ^ 40 * 3298409 * 2
def baseEnd_3298409 : Nat := 564556404038630231106133

theorem tailTrace_3298409 : CollatzResearch.WordTrace tailWord_3298409 prefixEnd_3298409 564556404038630231106133 := by
  unfold tailWord_3298409
  simp only [CollatzResearch.WordTrace]
  refine ⟨120302859507434991253842281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80201906338289994169228187 120302859507434991253842281)
  ·
    refine ⟨90227144630576243440381711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120302859507434991253842281 90227144630576243440381711)
    ·
      refine ⟨135340716945864365160572567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90227144630576243440381711 135340716945864365160572567)
      ·
        refine ⟨203011075418796547740858851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135340716945864365160572567 203011075418796547740858851)
        ·
          refine ⟨304516613128194821611288277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203011075418796547740858851 304516613128194821611288277)
          ·
            refine ⟨7137108120192066131514569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 304516613128194821611288277 7137108120192066131514569)
            ·
              refine ⟨5352831090144049598635927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7137108120192066131514569 5352831090144049598635927)
              ·
                refine ⟨8029246635216074397953891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5352831090144049598635927 8029246635216074397953891)
                ·
                  refine ⟨12043869952824111596930837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8029246635216074397953891 12043869952824111596930837)
                  ·
                    refine ⟨564556404038630231106133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12043869952824111596930837 564556404038630231106133)
                    ·
                      rfl

theorem cell23_3298409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 6].length) (baseStart_3298409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298409 prefixEnd_3298409 := by exact prefixLift 3298409
  have htrace : WordTrace (prefixWord ++ tailWord_3298409) baseStart_3298409 baseEnd_3298409 := by
    simpa [prefixWord, tailWord_3298409, baseEnd_3298409] using wordTrace_append hprefix tailTrace_3298409
  have hstable : (prefixWord ++ tailWord_3298409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298409).length < 2 ^ (prefixWord ++ tailWord_3298409).sum := by decide
  have hdescent : baseEnd_3298409 < baseStart_3298409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298429 : List Nat := [1, 4, 1, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_3298429 : Nat := 118140960795 + 3298429 * 2 ^ 59
def prefixEnd_3298429 : Nat := 4983230072969 + 3 ^ 40 * 3298429 * 2
def baseEnd_3298429 : Nat := 1693679481728980615068307

theorem tailTrace_3298429 : CollatzResearch.WordTrace tailWord_3298429 prefixEnd_3298429 1693679481728980615068307 := by
  unfold tailWord_3298429
  simp only [CollatzResearch.WordTrace]
  refine ⟨120303588967362534669570341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80202392644908356446380227 120303588967362534669570341)
  ·
    refine ⟨22556922931380475250544439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120303588967362534669570341 22556922931380475250544439)
    ·
      refine ⟨33835384397070712875816659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22556922931380475250544439 33835384397070712875816659)
      ·
        refine ⟨50753076595606069313724989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33835384397070712875816659 50753076595606069313724989)
        ·
          refine ⟨19032403723352275992646871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50753076595606069313724989 19032403723352275992646871)
          ·
            refine ⟨28548605585028413988970307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19032403723352275992646871 28548605585028413988970307)
            ·
              refine ⟨42822908377542620983455461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28548605585028413988970307 42822908377542620983455461)
              ·
                refine ⟨8029295320789241434397899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42822908377542620983455461 8029295320789241434397899)
                ·
                  refine ⟨12043942981183862151596849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8029295320789241434397899 12043942981183862151596849)
                  ·
                    refine ⟨9032957235887896613697637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12043942981183862151596849 9032957235887896613697637)
                    ·
                      refine ⟨1693679481728980615068307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9032957235887896613697637 1693679481728980615068307)
                      ·
                        rfl

theorem cell23_3298429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_3298429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298429 prefixEnd_3298429 := by exact prefixLift 3298429
  have htrace : WordTrace (prefixWord ++ tailWord_3298429) baseStart_3298429 baseEnd_3298429 := by
    simpa [prefixWord, tailWord_3298429, baseEnd_3298429] using wordTrace_append hprefix tailTrace_3298429
  have hstable : (prefixWord ++ tailWord_3298429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298429).length < 2 ^ (prefixWord ++ tailWord_3298429).sum := by decide
  have hdescent : baseEnd_3298429 < baseStart_3298429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298433 : List Nat := [1, 2, 4, 2, 2, 1, 4, 1, 1, 1, 4]
def baseStart_3298433 : Nat := 118140960795 + 3298433 * 2 ^ 59
def prefixEnd_3298433 : Nat := 4983230072969 + 3 ^ 40 * 3298433 * 2
def baseEnd_3298433 : Nat := 1693681535651598599418289

theorem tailTrace_3298433 : CollatzResearch.WordTrace tailWord_3298433 prefixEnd_3298433 1693681535651598599418289 := by
  unfold tailWord_3298433
  simp only [CollatzResearch.WordTrace]
  refine ⟨120303734859348043352715953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80202489906232028901810635 120303734859348043352715953)
  ·
    refine ⟨90227801144511032514536965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120303734859348043352715953 90227801144511032514536965)
    ·
      refine ⟨16917712714595818596475681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90227801144511032514536965 16917712714595818596475681)
      ·
        refine ⟨12688284535946863947356761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16917712714595818596475681 12688284535946863947356761)
        ·
          refine ⟨9516213401960147960517571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12688284535946863947356761 9516213401960147960517571)
          ·
            refine ⟨14274320102940221940776357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9516213401960147960517571 14274320102940221940776357)
            ·
              refine ⟨2676435019301291613895567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14274320102940221940776357 2676435019301291613895567)
              ·
                refine ⟨4014652528951937420843351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676435019301291613895567 4014652528951937420843351)
                ·
                  refine ⟨6021978793427906131265027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4014652528951937420843351 6021978793427906131265027)
                  ·
                    refine ⟨9032968190141859196897541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6021978793427906131265027 9032968190141859196897541)
                    ·
                      refine ⟨1693681535651598599418289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9032968190141859196897541 1693681535651598599418289)
                      ·
                        rfl

theorem cell23_3298433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_3298433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298433 prefixEnd_3298433 := by exact prefixLift 3298433
  have htrace : WordTrace (prefixWord ++ tailWord_3298433) baseStart_3298433 baseEnd_3298433 := by
    simpa [prefixWord, tailWord_3298433, baseEnd_3298433] using wordTrace_append hprefix tailTrace_3298433
  have hstable : (prefixWord ++ tailWord_3298433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298433).length < 2 ^ (prefixWord ++ tailWord_3298433).sum := by decide
  have hdescent : baseEnd_3298433 < baseStart_3298433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298450 : List Nat := [3, 2, 3, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_3298450 : Nat := 118140960795 + 3298450 * 2 ^ 59
def prefixEnd_3298450 : Nat := 4983230072969 + 3 ^ 40 * 3298450 * 2
def baseEnd_3298450 : Nat := 1693690264822725032905711

theorem tailTrace_3298450 : CollatzResearch.WordTrace tailWord_3298450 prefixEnd_3298450 1693690264822725032905711 := by
  unfold tailWord_3298450
  simp only [CollatzResearch.WordTrace]
  refine ⟨30076088725071613814021201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80202903266857636837389869 30076088725071613814021201)
  ·
    refine ⟨22557066543803710360515901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30076088725071613814021201 22557066543803710360515901)
    ·
      refine ⟨8458899953926391385193463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22557066543803710360515901 8458899953926391385193463)
      ·
        refine ⟨12688349930889587077790195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8458899953926391385193463 12688349930889587077790195)
        ·
          refine ⟨19032524896334380616685293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12688349930889587077790195 19032524896334380616685293)
          ·
            refine ⟨7137196836125392731256985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19032524896334380616685293 7137196836125392731256985)
            ·
              refine ⟨5352897627094044548442739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7137196836125392731256985 5352897627094044548442739)
              ·
                refine ⟨8029346440641066822664109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5352897627094044548442739 8029346440641066822664109)
                ·
                  refine ⟨3011004915240400058499041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8029346440641066822664109 3011004915240400058499041)
                  ·
                    refine ⟨2258253686430300043874281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3011004915240400058499041 2258253686430300043874281)
                    ·
                      refine ⟨1693690264822725032905711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2258253686430300043874281 1693690264822725032905711)
                      ·
                        rfl

theorem cell23_3298450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_3298450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298450 prefixEnd_3298450 := by exact prefixLift 3298450
  have htrace : WordTrace (prefixWord ++ tailWord_3298450) baseStart_3298450 baseEnd_3298450 := by
    simpa [prefixWord, tailWord_3298450, baseEnd_3298450] using wordTrace_append hprefix tailTrace_3298450
  have hstable : (prefixWord ++ tailWord_3298450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298450).length < 2 ^ (prefixWord ++ tailWord_3298450).sum := by decide
  have hdescent : baseEnd_3298450 < baseStart_3298450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298459 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 1, 9, 2]
def baseStart_3298459 : Nat := 118140960795 + 3298459 * 2 ^ 59
def prefixEnd_3298459 : Nat := 4983230072969 + 3 ^ 40 * 3298459 * 2
def baseEnd_3298459 : Nat := 1693694886148615497693169

theorem tailTrace_3298459 : CollatzResearch.WordTrace tailWord_3298459 prefixEnd_3298459 1693694886148615497693169 := by
  unfold tailWord_3298459
  simp only [CollatzResearch.WordTrace]
  refine ⟨120304683157253849793162431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80203122104835899862108287 120304683157253849793162431)
  ·
    refine ⟨180457024735880774689743647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120304683157253849793162431 180457024735880774689743647)
    ·
      refine ⟨270685537103821162034615471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180457024735880774689743647 270685537103821162034615471)
      ·
        refine ⟨406028305655731743051923207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270685537103821162034615471 406028305655731743051923207)
        ·
          refine ⟨609042458483597614577884811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406028305655731743051923207 609042458483597614577884811)
          ·
            refine ⟨913563687725396421866827217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609042458483597614577884811 913563687725396421866827217)
            ·
              refine ⟨685172765794047316400120413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 913563687725396421866827217 685172765794047316400120413)
              ·
                refine ⟨256939787172767743650045155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 685172765794047316400120413 256939787172767743650045155)
                ·
                  refine ⟨385409680759151615475067733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256939787172767743650045155 385409680759151615475067733)
                  ·
                    refine ⟨2258259848198153996924225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 385409680759151615475067733 2258259848198153996924225)
                    ·
                      refine ⟨1693694886148615497693169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2258259848198153996924225 1693694886148615497693169)
                      ·
                        rfl

theorem cell23_3298459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 9, 2].length) (baseStart_3298459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298459 prefixEnd_3298459 := by exact prefixLift 3298459
  have htrace : WordTrace (prefixWord ++ tailWord_3298459) baseStart_3298459 baseEnd_3298459 := by
    simpa [prefixWord, tailWord_3298459, baseEnd_3298459] using wordTrace_append hprefix tailTrace_3298459
  have hstable : (prefixWord ++ tailWord_3298459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298459).length < 2 ^ (prefixWord ++ tailWord_3298459).sum := by decide
  have hdescent : baseEnd_3298459 < baseStart_3298459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298463 : List Nat := [1, 1, 2, 6, 2, 2, 1, 1, 1, 2, 4]
def baseStart_3298463 : Nat := 118140960795 + 3298463 * 2 ^ 59
def prefixEnd_3298463 : Nat := 4983230072969 + 3 ^ 40 * 3298463 * 2
def baseEnd_3298463 : Nat := 1693696940071233482043151

theorem tailTrace_3298463 : CollatzResearch.WordTrace tailWord_3298463 prefixEnd_3298463 1693696940071233482043151 := by
  unfold tailWord_3298463
  simp only [CollatzResearch.WordTrace]
  refine ⟨120304829049239358476308043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80203219366159572317538695 120304829049239358476308043)
  ·
    refine ⟨180457243573859037714462065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120304829049239358476308043 180457243573859037714462065)
    ·
      refine ⟨135342932680394278285846549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180457243573859037714462065 135342932680394278285846549)
      ·
        refine ⟨6344199969393481794649057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 135342932680394278285846549 6344199969393481794649057)
        ·
          refine ⟨4758149977045111345986793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6344199969393481794649057 4758149977045111345986793)
          ·
            refine ⟨3568612482783833509490095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4758149977045111345986793 3568612482783833509490095)
            ·
              refine ⟨5352918724175750264235143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3568612482783833509490095 5352918724175750264235143)
              ·
                refine ⟨8029378086263625396352715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5352918724175750264235143 8029378086263625396352715)
                ·
                  refine ⟨12044067129395438094529073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8029378086263625396352715 12044067129395438094529073)
                  ·
                    refine ⟨9033050347046578570896805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12044067129395438094529073 9033050347046578570896805)
                    ·
                      refine ⟨1693696940071233482043151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9033050347046578570896805 1693696940071233482043151)
                      ·
                        rfl

theorem cell23_3298463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_3298463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298463 prefixEnd_3298463 := by exact prefixLift 3298463
  have htrace : WordTrace (prefixWord ++ tailWord_3298463) baseStart_3298463 baseEnd_3298463 := by
    simpa [prefixWord, tailWord_3298463, baseEnd_3298463] using wordTrace_append hprefix tailTrace_3298463
  have hstable : (prefixWord ++ tailWord_3298463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298463).length < 2 ^ (prefixWord ++ tailWord_3298463).sum := by decide
  have hdescent : baseEnd_3298463 < baseStart_3298463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298493 : List Nat := [1, 4, 1, 2, 1, 1, 4, 3, 1, 3, 2]
def baseStart_3298493 : Nat := 118140960795 + 3298493 * 2 ^ 59
def prefixEnd_3298493 : Nat := 4983230072969 + 3 ^ 40 * 3298493 * 2
def baseEnd_3298493 : Nat := 1693712344490868364668013

theorem tailTrace_3298493 : CollatzResearch.WordTrace tailWord_3298493 prefixEnd_3298493 1693712344490868364668013 := by
  unfold tailWord_3298493
  simp only [CollatzResearch.WordTrace]
  refine ⟨120305923239130673599900133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80203948826087115733266755 120305923239130673599900133)
  ·
    refine ⟨22557360607337001299981275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120305923239130673599900133 22557360607337001299981275)
    ·
      refine ⟨33836040911005501949971913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22557360607337001299981275 33836040911005501949971913)
      ·
        refine ⟨25377030683254126462478935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33836040911005501949971913 25377030683254126462478935)
        ·
          refine ⟨38065546024881189693718403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25377030683254126462478935 38065546024881189693718403)
          ·
            refine ⟨57098319037321784540577605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38065546024881189693718403 57098319037321784540577605)
            ·
              refine ⟨10705934819497834601358301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57098319037321784540577605 10705934819497834601358301)
              ·
                refine ⟨4014725557311687975509363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10705934819497834601358301 4014725557311687975509363)
                ·
                  refine ⟨6022088335967531963264045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4014725557311687975509363 6022088335967531963264045)
                  ·
                    refine ⟨2258283125987824486224017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6022088335967531963264045 2258283125987824486224017)
                    ·
                      refine ⟨1693712344490868364668013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2258283125987824486224017 1693712344490868364668013)
                      ·
                        rfl

theorem cell23_3298493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_3298493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298493 prefixEnd_3298493 := by exact prefixLift 3298493
  have htrace : WordTrace (prefixWord ++ tailWord_3298493) baseStart_3298493 baseEnd_3298493 := by
    simpa [prefixWord, tailWord_3298493, baseEnd_3298493] using wordTrace_append hprefix tailTrace_3298493
  have hstable : (prefixWord ++ tailWord_3298493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298493).length < 2 ^ (prefixWord ++ tailWord_3298493).sum := by decide
  have hdescent : baseEnd_3298493 < baseStart_3298493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298517 : List Nat := [1, 3, 2, 4, 1, 3, 2, 1, 2, 1, 3]
def baseStart_3298517 : Nat := 118140960795 + 3298517 * 2 ^ 59
def prefixEnd_3298517 : Nat := 4983230072969 + 3 ^ 40 * 3298517 * 2
def baseEnd_3298517 : Nat := 1693724668026576270767903

theorem tailTrace_3298517 : CollatzResearch.WordTrace tailWord_3298517 prefixEnd_3298517 1693724668026576270767903 := by
  unfold tailWord_3298517
  simp only [CollatzResearch.WordTrace]
  refine ⟨120306798591043725698773805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80204532394029150465849203 120306798591043725698773805)
  ·
    refine ⟨45115049471641397137040177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120306798591043725698773805 45115049471641397137040177)
    ·
      refine ⟨33836287103731047852780133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45115049471641397137040177 33836287103731047852780133)
      ·
        refine ⟨6344303831949571472396275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33836287103731047852780133 6344303831949571472396275)
        ·
          refine ⟨9516455747924357208594413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6344303831949571472396275 9516455747924357208594413)
          ·
            refine ⟨3568670905471633953222905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9516455747924357208594413 3568670905471633953222905)
            ·
              refine ⟨2676503179103725464917179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3568670905471633953222905 2676503179103725464917179)
              ·
                refine ⟨4014754768655588197375769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676503179103725464917179 4014754768655588197375769)
                ·
                  refine ⟨3011066076491691148031827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4014754768655588197375769 3011066076491691148031827)
                  ·
                    refine ⟨4516599114737536722047741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3011066076491691148031827 4516599114737536722047741)
                    ·
                      refine ⟨1693724668026576270767903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4516599114737536722047741 1693724668026576270767903)
                      ·
                        rfl

theorem cell23_3298517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_3298517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298517 prefixEnd_3298517 := by exact prefixLift 3298517
  have htrace : WordTrace (prefixWord ++ tailWord_3298517) baseStart_3298517 baseEnd_3298517 := by
    simpa [prefixWord, tailWord_3298517, baseEnd_3298517] using wordTrace_append hprefix tailTrace_3298517
  have hstable : (prefixWord ++ tailWord_3298517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298517).length < 2 ^ (prefixWord ++ tailWord_3298517).sum := by decide
  have hdescent : baseEnd_3298517 < baseStart_3298517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298519 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 4]
def baseStart_3298519 : Nat := 118140960795 + 3298519 * 2 ^ 59
def prefixEnd_3298519 : Nat := 4983230072969 + 3 ^ 40 * 3298519 * 2
def baseEnd_3298519 : Nat := 1693725694987885262942893

theorem tailTrace_3298519 : CollatzResearch.WordTrace tailWord_3298519 prefixEnd_3298519 1693725694987885262942893 := by
  unfold tailWord_3298519
  simp only [CollatzResearch.WordTrace]
  refine ⟨120306871537036480040346611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80204581024690986693564407 120306871537036480040346611)
  ·
    refine ⟨180460307305554720060519917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120306871537036480040346611 180460307305554720060519917)
    ·
      refine ⟨67672615239583020022694969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180460307305554720060519917 67672615239583020022694969)
      ·
        refine ⟨50754461429687265017021227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67672615239583020022694969 50754461429687265017021227)
        ·
          refine ⟨76131692144530897525531841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50754461429687265017021227 76131692144530897525531841)
          ·
            refine ⟨57098769108398173144148881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76131692144530897525531841 57098769108398173144148881)
            ·
              refine ⟨42824076831298629858111661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57098769108398173144148881 42824076831298629858111661)
              ·
                refine ⟨16059028811736986196791873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42824076831298629858111661 16059028811736986196791873)
                ·
                  refine ⟨12044271608802739647593905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16059028811736986196791873 12044271608802739647593905)
                  ·
                    refine ⟨9033203706602054735695429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12044271608802739647593905 9033203706602054735695429)
                    ·
                      refine ⟨1693725694987885262942893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9033203706602054735695429 1693725694987885262942893)
                      ·
                        rfl

theorem cell23_3298519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_3298519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298519 prefixEnd_3298519 := by exact prefixLift 3298519
  have htrace : WordTrace (prefixWord ++ tailWord_3298519) baseStart_3298519 baseEnd_3298519 := by
    simpa [prefixWord, tailWord_3298519, baseEnd_3298519] using wordTrace_append hprefix tailTrace_3298519
  have hstable : (prefixWord ++ tailWord_3298519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298519).length < 2 ^ (prefixWord ++ tailWord_3298519).sum := by decide
  have hdescent : baseEnd_3298519 < baseStart_3298519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298563 : List Nat := [1, 1, 1, 3, 2, 4, 4, 2, 5]
def baseStart_3298563 : Nat := 118140960795 + 3298563 * 2 ^ 59
def prefixEnd_3298563 : Nat := 4983230072969 + 3 ^ 40 * 3298563 * 2
def baseEnd_3298563 : Nat := 188194254237409232310299

theorem tailTrace_3298563 : CollatzResearch.WordTrace tailWord_3298563 prefixEnd_3298563 188194254237409232310299 := by
  unfold tailWord_3298563
  simp only [CollatzResearch.WordTrace]
  refine ⟨120308476348877075554948343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80205650899251383703298895 120308476348877075554948343)
  ·
    refine ⟨180462714523315613332422515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120308476348877075554948343 180462714523315613332422515)
    ·
      refine ⟨270694071784973419998633773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180462714523315613332422515 270694071784973419998633773)
      ·
        refine ⟨101510276919365032499487665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270694071784973419998633773 101510276919365032499487665)
        ·
          refine ⟨76132707689523774374615749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101510276919365032499487665 76132707689523774374615749)
          ·
            refine ⟨14274882691785707695240453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76132707689523774374615749 14274882691785707695240453)
            ·
              refine ⟨2676540504709820192857585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14274882691785707695240453 2676540504709820192857585)
              ·
                refine ⟨2007405378532365144643189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2676540504709820192857585 2007405378532365144643189)
                ·
                  refine ⟨188194254237409232310299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2007405378532365144643189 188194254237409232310299)
                  ·
                    rfl

theorem cell23_3298563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 5].length) (baseStart_3298563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298563 prefixEnd_3298563 := by exact prefixLift 3298563
  have htrace : WordTrace (prefixWord ++ tailWord_3298563) baseStart_3298563 baseEnd_3298563 := by
    simpa [prefixWord, tailWord_3298563, baseEnd_3298563] using wordTrace_append hprefix tailTrace_3298563
  have hstable : (prefixWord ++ tailWord_3298563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298563).length < 2 ^ (prefixWord ++ tailWord_3298563).sum := by decide
  have hdescent : baseEnd_3298563 < baseStart_3298563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298569 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 1, 2, 5]
def baseStart_3298569 : Nat := 118140960795 + 3298569 * 2 ^ 59
def prefixEnd_3298569 : Nat := 4983230072969 + 3 ^ 40 * 3298569 * 2
def baseEnd_3298569 : Nat := 1693751369020610067317663

theorem tailTrace_3298569 : CollatzResearch.WordTrace tailWord_3298569 prefixEnd_3298569 1693751369020610067317663 := by
  unfold tailWord_3298569
  simp only [CollatzResearch.WordTrace]
  refine ⟨120308695186855338579666761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80205796791236892386444507 120308695186855338579666761)
  ·
    refine ⟨90231521390141503934750071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120308695186855338579666761 90231521390141503934750071)
    ·
      refine ⟨135347282085212255902125107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90231521390141503934750071 135347282085212255902125107)
      ·
        refine ⟨203020923127818383853187661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135347282085212255902125107 203020923127818383853187661)
        ·
          refine ⟨76132846172931893944945373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203020923127818383853187661 76132846172931893944945373)
          ·
            refine ⟨28549817314849460229354515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76132846172931893944945373 28549817314849460229354515)
            ·
              refine ⟨42824725972274190344031773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28549817314849460229354515 42824725972274190344031773)
              ·
                refine ⟨16059272239602821379011915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42824725972274190344031773 16059272239602821379011915)
                ·
                  refine ⟨24088908359404232068517873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16059272239602821379011915 24088908359404232068517873)
                  ·
                    refine ⟨18066681269553174051388405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24088908359404232068517873 18066681269553174051388405)
                    ·
                      refine ⟨1693751369020610067317663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18066681269553174051388405 1693751369020610067317663)
                      ·
                        rfl

theorem cell23_3298569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_3298569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298569 prefixEnd_3298569 := by exact prefixLift 3298569
  have htrace : WordTrace (prefixWord ++ tailWord_3298569) baseStart_3298569 baseEnd_3298569 := by
    simpa [prefixWord, tailWord_3298569, baseEnd_3298569] using wordTrace_append hprefix tailTrace_3298569
  have hstable : (prefixWord ++ tailWord_3298569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298569).length < 2 ^ (prefixWord ++ tailWord_3298569).sum := by decide
  have hdescent : baseEnd_3298569 < baseStart_3298569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
